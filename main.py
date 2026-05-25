import discord
from discord import app_commands
from discord.http import Route
from discord.ext import tasks
import time
import os
import json
import re
import random
import asyncio
import aiohttp
import unicodedata
from datetime import timedelta
from collections import defaultdict

TOKEN           = os.environ["DISCORD_TOKEN"]
LOG_CHANNEL_ID  = 1507510607807647768

VOICE_CHANNELS = [
    (1507510608310960312, "🎤 Main Voice Room"),
    (1507510608310960313, "🎤 Second Voice Room"),
]
MONITORED_IDS = {ch_id for ch_id, _ in VOICE_CHANNELS}

BAD_WORDS_FILE = os.path.join(os.path.dirname(__file__), "badwords.json")
STATS_FILE     = os.path.join(os.path.dirname(__file__), "stats.json")
WARNINGS_FILE  = os.path.join(os.path.dirname(__file__), "warnings.json")

RAID_THRESHOLD = 5
RAID_WINDOW    = 10
RAID_COOLDOWN  = 300

smart_filter_enabled: dict[int, bool] = {}  # guild_id -> True/False (default True)

# ─── State ────────────────────────────────────────────────────────────────────
afk_users:        dict[int, tuple[str, float]] = {}
start_times:      dict[int, float]             = {}
channel_members:  dict[int, set]               = {ch_id: set() for ch_id, _ in VOICE_CHANNELS}
recent_joins:     dict[int, list]              = defaultdict(list)
raid_mode:        dict[int, float]             = {}
_sticker_cache:   dict[int, list]             = {}
vc_clients:       dict[int, discord.VoiceClient] = {}  # guild_id → active VoiceClient

# ─── Intents ──────────────────────────────────────────────────────────────────
intents = discord.Intents.default()
intents.voice_states    = True
intents.message_content = True
intents.members         = True

client = discord.Client(intents=intents)
tree   = app_commands.CommandTree(client)

# ─── Helpers ──────────────────────────────────────────────────────────────────
def load_json(path: str) -> dict:
    if os.path.exists(path):
        with open(path, "r", encoding="utf-8") as f:
            return json.load(f)
    return {}

def save_json(path: str, data):
    with open(path, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2, ensure_ascii=False)

def load_bad_words() -> list:
    if os.path.exists(BAD_WORDS_FILE):
        with open(BAD_WORDS_FILE, "r", encoding="utf-8") as f:
            return json.load(f)
    return []

def save_bad_words(words: list):
    save_json(BAD_WORDS_FILE, words)

def add_session_time(channel_id: int, seconds: int):
    stats = load_json(STATS_FILE)
    key = str(channel_id)
    stats[key] = stats.get(key, 0) + seconds
    save_json(STATS_FILE, stats)

def get_total_seconds(channel_id: int) -> int:
    return load_json(STATS_FILE).get(str(channel_id), 0)

def parse_duration(text: str) -> int | None:
    match = re.fullmatch(r"(\d+)([smhd])", text.lower())
    if not match:
        return None
    amount, unit = int(match.group(1)), match.group(2)
    return amount * {"s": 1, "m": 60, "h": 3600, "d": 86400}[unit]

def format_elapsed(seconds: int) -> str:
    mins, secs = divmod(seconds, 60)
    hours, mins = divmod(mins, 60)
    return f"{hours:02d}:{mins:02d}:{secs:02d}"

def format_total(seconds: int) -> str:
    hours, rem = divmod(seconds, 3600)
    return f"{hours}h {rem // 60}m"

# ══════════════════════════════════════════════════════════════════════════════
#  SMART FILTER
# ══════════════════════════════════════════════════════════════════════════════

def _normalize(text: str) -> str:
    """Normalize romanized/latin text for pattern matching — strips evasion chars."""
    text = text.lower()
    text = unicodedata.normalize("NFKD", text)
    subs = {
        '0':'o','1':'i','2':'z','3':'e','4':'a','5':'s','6':'g',
        '7':'h','8':'b','9':'g','@':'a','$':'s','!':'i','+':'t',
        '|':'i','(':'c',')':'','*':'','.':'',',':'','-':'','_':'',
        ' ':'','\t':'',
        # Arabic diacritics
        'ً':'','ٌ':'','ٍ':'','َ':'','ُ':'','ِ':'','ّ':'','ْ':'',
    }
    for old, new in subs.items():
        text = text.replace(old, new)
    # Collapse 3+ repeated chars to 2 (ffuucckk → ffuck stays, fff→ff)
    text = re.sub(r'(.)\1{2,}', r'\1\1', text)
    return text

def _arabic_normalize(text: str) -> str:
    """Strip ALL non-Arabic-letter chars and normalize letter forms.
    Catches: spaced letters (ك س م), dotted (ك.س.م), tatweeled (كـسـم),
    alef variants (أإآا), ta-marbuta/ha, ya/alef-maqsura."""
    # Keep only Arabic Unicode block letters
    text = re.sub(r'[^\u0621-\u063A\u0641-\u064A]', '', text)
    # Normalize alef forms → bare alef
    text = re.sub(r'[أإآٱٲٳ]', 'ا', text)
    # ta-marbuta → ha (ة → ه)
    text = text.replace('ة', 'ه')
    # alef maqsura → ya (ى → ي)
    text = text.replace('ى', 'ي')
    # waw with hamza → waw
    text = text.replace('ؤ', 'و')
    # ya with hamza → ya
    text = text.replace('ئ', 'ي')
    return text

# ─── Arabic bad words (script) ────────────────────────────────────────────────
# The matcher checks both raw text AND fully-stripped/normalized Arabic text,
# so entries here catch: "كسم", "ك س م", "ك.س.م", "كـسـم", "كسمة" → "كسمه", etc.

_ARABIC_BAD = [
    # كس — kos (vagina, primary insult)
    'كس','كسك','كسم','كسمك','كسمه','كسمها','كسمهم','كسمي',
    'كس امك','كس اختك','كس اخوك','كس امه','كس امها',
    # زب — zeb (penis)
    'زب','زبي','زبك','زبه','زبها','زبهم',
    # شرموطة — sharmouta (whore)
    'شرموط','شرموطه','شرموطة','شراميط','شرامط',
    # نيك — neek (fuck)
    'نيك','انيك','بنيك','ينيك','هينيك','بينيك',
    'متناك','متناكه','متناكة','اتناك','اتناكت',
    'بتتناك','هيتناك','منيوك','مناك','مناكه',
    'ينيكك','هينيكك','انيكك','نيكك',
    # خول — khawal (gay slur)
    'خول','خوله','خولة','خولات','خوالين',
    # عرص — 3rs (pimp, coward slur)
    'عرص','عرصه','عرصة','عرصات','عرصين',
    # أير — air (penis)
    'اير','ايره','ايرك','ايري','ايرها','ايرهم',
    'ايرك في','ايري في',
    # طيز — teez (ass)
    'طيز','طيزك','طيزه','طيزها','طيزي','طيزهم',
    # خرا — khara (shit)
    'خرا','خره','خرة','خاره',
    # قحبة — a7ba (whore)
    'قحبه','قحبة','قحب','قحبتك','قحبته',
    # لبوه — labwa (whore, lioness slur)
    'لبوه','لبوهه','لبوهة','لبوات',
    # وسخ — wesekh (filthy)
    'وسخ','وسخه','وسخة','وسخين',
    # مص — moss (suck — sexual)
    'امص','بتمص','بيمص','تمص','يمص','مصمص',
    # حيوان / بهيمة — animal insults
    'حيوان','حيوانه','حيوانة','بهيمه','بهيمة','بهايم',
    # ابن ... compound insults
    'ابن المتناكه','ابن المتناكة','ابن الشرموطه','ابن الشرموطة',
    'ابن الكلبه','ابن الكلبة','ابن القحبه','ابن القحبة',
    'ابن الوسخه','ابن الوسخة','ابن الحيوان',
    'ابن متناكه','ابن شرموطه','ابن كلبه','ابن قحبه',
    'بنت شرموطه','بنت متناكه','بنت قحبه','بنت الكلب',
    # يلعن — curse phrases
    'يلعن','يلعن امك','يلعن ابوك','يلعن اخوك',
    'يلعن دينك','يلعن دينه','يلعن دينها',
    'العنك','العن امك',
    # زفت — zeft (tar, insult)
    'زفت','زفته','زفتة',
    # كلب — kalb (dog insult)
    'كلب','كلبه','كلبة','كلاب',
    'ابن الكلب','بنت الكلب',
]

# Pre-normalized version for catching spaced/evasion writing
_ARABIC_BAD_NORM = [_arabic_normalize(w) for w in _ARABIC_BAD]

# ─── Romanized / mixed patterns ───────────────────────────────────────────────

_SMART_PATTERNS = [
    # ── English ──────────────────────────────────────────────────────────────
    r'f+u+c+k+', r'f+u+q+', r'ph+u+c+k',
    r's+h+i+t+',
    r'b+i+t+c+h+',
    r'c+u+n+t+',
    r'a+s+s+h+o+l+e+',
    r'wh+o+r+e+',
    r'n+i+g+g+[ae]+r?',
    r'f+a+g+g?[oi]+t?',
    r'\bd+i+c+k+\b',
    r'\bc+o+c+k+\b',
    r'p+u+s+s+y+',
    r'b+a+s+t+[ae]+r+d+',
    r'm+o+t+h+[ae]+r+f+u+c+k',
    r'r+e+t+a+r+d+',
    r'sl+u+t+',
    r'd+u+m+b+a+s+s',

    # ── كس — kos / kus / kes / ks ────────────────────────────────────────────
    r'\bk+[oue]*s+\b',                      # ks, kos, kus, kes
    r'k+[oue]+s+[sek]*',                    # kos, kosss, kosk
    r'k+[oue]*[sz]+[o]?m+[aeki]*',          # kosm, kosomak, kosmak
    r'k+s+m+[aek]*',                        # ksm, ksmk (abbreviated)
    r'k+o+s+o+m+[aek]+',                    # kosomak
    r'k+[oue]+s+\s*(a|el|al|om|um|okh|akh)', # kos omak / kos omak / kos okhtak

    # ── زب — zeb / zib / zb ──────────────────────────────────────────────────
    r'\bz+[ei]*b+[iy]?\b',                  # zb, zeb, zib, zebi

    # ── شرموطة — sharmouta / shrmouta ────────────────────────────────────────
    r'sh+[ae]*r+m+[o0u]+[ou]*t+[aeh]?',    # sharmouta, shrmouta
    r's+[hj]+r+m+t+[aeh]?',                 # shr mt (abbreviated)

    # ── نيك — neek / nik / n*k ───────────────────────────────────────────────
    r'\bn+[iey]+[e]*[ck]+[aek]?\b',         # nik, neek, neka
    r'\bn[iy]k\b',                           # nyk, nik (bare)
    r'm+[ae]+n+[yi]+[o0]+[ck]+',            # manyok, mniok, manyak
    r'm+[ae]+t+n+[ae]*[ck]+',              # metneak, metnak
    r'[ae]*t+n+[ae]+[ck]+',                # etnak, atnak

    # ── أير — air / eyr / ayr (penis) ────────────────────────────────────────
    r'\b[ae]+[yi]+r+[iy]?\b',               # air, eyr, ayr, ayri

    # ── طيز — teez / tiz / tz ────────────────────────────────────────────────
    r'\bt+[ei]*[e]*z+\b',                   # tz, tiz, teez, teezak

    # ── خرا — khara / 5ara / khra ────────────────────────────────────────────
    r'kh+[ae]+r+[ae]?',                     # khara, khra
    r'5+[ae]*r+[ae]?',                       # 5ara, 5ra

    # ── عرص — 3rs / 3ars ─────────────────────────────────────────────────────
    r'\b[3e]+r+s+[aeh]?\b',                 # 3rs, 3arsa, ers

    # ── خول — khawal / 5awal / khwl ──────────────────────────────────────────
    r'kh+[ao]*w+[ae]+l+',                   # khawal, khwal
    r'5+[ao]*w+[ae]+l+',                    # 5awal, 5wal
    r'\bkhwl\b',                             # abbreviated

    # ── قحبة — a7ba / qa7ba / 2a7ba ──────────────────────────────────────────
    r'[q2]*[ae]+[7h]+b+[aeh]?',             # a7ba, qa7ba, 2a7ba
    r'\ba[hj]b[aeh]?\b',                    # ahba, ajba (h/j for 7)

    # ── وسخ — wesekh / wsekh / ws5 ───────────────────────────────────────────
    r'w+[e3]+s+[e3]*[ck5]+[h]?',            # wesekh, ws5, wsk

    # ── لبوه — labwa / labwa ──────────────────────────────────────────────────
    r'l+[ao]+b+w+[aeh]?',                   # labwa, labwah

    # ── مص — moss (suck — sexual) ─────────────────────────────────────────────
    r'\bm+[ou]+s+s*\b',                     # mos, moss (can false-positive — kept tight)
    r'[ae]+m+[ou]+s+',                      # amos, tmos
    r'b+[iy]+t+m+[ou]+s+',                  # bitmoss

    # ── ابن / ibn compound ────────────────────────────────────────────────────
    r'ibn\s*[a-z]*.{0,6}(sharm|metn|kos|qah|weskh|kalb|klb)',
    r'ebn\s*[a-z]*.{0,6}(sharm|metn|kos|qah|weskh|kalb|klb)',

    # ── يلعن — yal3an ────────────────────────────────────────────────────────
    r'y+[ae]+l+[3a]+[ae]*n+',               # yal3an, yalaan

    # ── زفت — zeft ───────────────────────────────────────────────────────────
    r'\bz+[ie]+f+t+\b',                     # zeft, zift
]

_COMPILED = [re.compile(p, re.IGNORECASE) for p in _SMART_PATTERNS]

def is_smart_bad(text: str) -> bool:
    # 1. Raw Arabic script check
    for word in _ARABIC_BAD:
        if word in text:
            return True
    # 2. Normalized Arabic check — catches spaced/dotted/tatweeled evasion
    #    e.g. "ك س م", "ك.س.م", "كـسـم", "كسمة" (ta-marbuta variant)
    norm_ar = _arabic_normalize(text)
    if norm_ar:
        for word_norm in _ARABIC_BAD_NORM:
            if word_norm and word_norm in norm_ar:
                return True
    # 3. Romanized pattern check on latin-normalized text
    norm = _normalize(text)
    original = text.lower()
    for pat in _COMPILED:
        if pat.search(norm) or pat.search(original):
            return True
    return False

def has_mod_perms(member: discord.Member) -> bool:
    return member.guild_permissions.administrator or member.guild_permissions.ban_members

def mod_embed(title: str, color: discord.Color, **fields) -> discord.Embed:
    embed = discord.Embed(title=title, color=color, timestamp=discord.utils.utcnow())
    for name, value in fields.items():
        embed.add_field(name=name, value=str(value), inline=True)
    return embed

async def log(guild: discord.Guild, embed: discord.Embed):
    ch = guild.get_channel(LOG_CHANNEL_ID)
    if ch:
        try:
            await ch.send(embed=embed)
        except discord.Forbidden:
            pass

# ─── Custom Emoji / Sticker helpers ───────────────────────────────────────────

def find_emoji(guild: discord.Guild, *keywords: str) -> str:
    for keyword in keywords:
        for emoji in guild.emojis:
            if keyword.lower() in emoji.name.lower():
                return str(emoji)
    return ""

async def get_stickers(guild: discord.Guild) -> list:
    if guild.id not in _sticker_cache:
        try:
            _sticker_cache[guild.id] = await guild.fetch_stickers()
        except Exception:
            _sticker_cache[guild.id] = []
    return _sticker_cache[guild.id]

async def find_sticker(guild: discord.Guild, *keywords: str):
    stickers = await get_stickers(guild)
    for keyword in keywords:
        for sticker in stickers:
            if keyword.lower() in sticker.name.lower():
                return sticker
    return None

async def send_sticker(channel, guild: discord.Guild, *keywords: str):
    sticker = await find_sticker(guild, *keywords)
    if sticker:
        try:
            await channel.send(stickers=[sticker])
        except (discord.Forbidden, discord.HTTPException):
            pass

async def set_voice_status(channel_id: int, status: str | None):
    try:
        await client.http.request(
            Route("PUT", "/channels/{channel_id}/voice-status", channel_id=channel_id),
            json={"status": status}
        )
    except discord.HTTPException as e:
        if e.status != 429:
            print(f"Voice status error: {e}")

async def add_warning(guild: discord.Guild, member: discord.Member, reason: str, moderator: str) -> int:
    warnings = load_json(WARNINGS_FILE)
    uid = str(member.id)
    if uid not in warnings:
        warnings[uid] = []
    warnings[uid].append({"reason": reason, "by": moderator, "time": time.time()})
    save_json(WARNINGS_FILE, warnings)
    count = len(warnings[uid])
    if count == 3:
        try:
            until = discord.utils.utcnow() + timedelta(days=1)
            await member.edit(timed_out_until=until, reason="Auto-mute: reached 3 warnings")
            try:
                dm_embed = discord.Embed(
                    title="🔇 You have been muted",
                    description=f"You have been automatically muted in **{guild.name}** for **1 day** after receiving 3 warnings.",
                    color=discord.Color.orange(),
                    timestamp=discord.utils.utcnow()
                )
                dm_embed.set_footer(text="Please follow the server rules when the mute expires.")
                await member.send(embed=dm_embed)
            except discord.Forbidden:
                pass
        except discord.Forbidden:
            pass
    if count >= 5:
        try:
            until = discord.utils.utcnow() + timedelta(weeks=1)
            await member.edit(timed_out_until=until, reason="Auto-mute: reached 5 warnings")
            try:
                dm_embed = discord.Embed(
                    title="🔇 You have been muted",
                    description=f"You have been automatically muted in **{guild.name}** for **1 week** after receiving 5 warnings.",
                    color=discord.Color.red(),
                    timestamp=discord.utils.utcnow()
                )
                dm_embed.set_footer(text="Please follow the server rules when the mute expires.")
                await member.send(embed=dm_embed)
            except discord.Forbidden:
                pass
        except discord.Forbidden:
            pass
    return count

async def dm_warning(member: discord.Member, reason: str, count: int, guild_name: str):
    try:
        embed = discord.Embed(
            title="⚠️ You have been warned!",
            description=f"You received a warning in **{guild_name}**.",
            color=discord.Color.yellow(),
            timestamp=discord.utils.utcnow()
        )
        embed.add_field(name="📝 Reason", value=reason, inline=False)
        embed.add_field(name="⚠️ Total Warnings", value=str(count), inline=True)
        embed.set_footer(text="Please follow the server rules to avoid further action.")
        await member.send(embed=embed)
    except discord.Forbidden:
        pass


# ─── UI Views ─────────────────────────────────────────────────────────────────

class DismissView(discord.ui.View):
    """Adds a dismiss button that lets the command invoker delete the bot's reply."""
    def __init__(self, user_id: int):
        super().__init__(timeout=300)
        self.user_id = user_id

    @discord.ui.button(label="🗑️ Dismiss", style=discord.ButtonStyle.secondary)
    async def dismiss(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.user_id:
            return await interaction.response.send_message("Only the person who ran this command can dismiss it.", ephemeral=True)
        await interaction.response.defer()
        await interaction.message.delete()

    async def on_timeout(self):
        for item in self.children:
            item.disabled = True


class PollView(discord.ui.View):
    """Adds a Close Poll button (mod or poll creator only)."""
    def __init__(self, author_id: int):
        super().__init__(timeout=None)
        self.author_id = author_id

    @discord.ui.button(label="🔒 Close Poll", style=discord.ButtonStyle.danger)
    async def close_poll(self, interaction: discord.Interaction, button: discord.ui.Button):
        if not has_mod_perms(interaction.user) and interaction.user.id != self.author_id:
            return await interaction.response.send_message("Only mods or the poll creator can close this.", ephemeral=True)
        try:
            await interaction.message.clear_reactions()
        except discord.Forbidden:
            pass
        button.disabled = True
        button.label = "🔒 Poll Closed"
        await interaction.message.edit(view=self)
        await interaction.response.send_message("✅ Poll closed.", ephemeral=True)


# ─── Events ───────────────────────────────────────────────────────────────────

@client.event
async def on_ready():
    for guild in client.guilds:
        tree.copy_global_to(guild=guild)
        synced = await tree.sync(guild=guild)
        print(f"🔄 Synced {len(synced)} commands to: {guild.name}")
    print(f"✅ Bot online as: {client.user}")
    print(f"📡 Monitoring {len(VOICE_CHANNELS)} voice channel(s) | Log: {LOG_CHANNEL_ID}")
    for guild in client.guilds:
        await get_stickers(guild)
        print(f"   🎭 {guild.name}: {len(guild.emojis)} custom emoji(s), {len(_sticker_cache.get(guild.id, []))} sticker(s) cached")
    for channel_id, _ in VOICE_CHANNELS:
        channel = client.get_channel(channel_id)
        if channel and isinstance(channel, discord.VoiceChannel):
            members_in = {m.id for m in channel.members if not m.bot}
            channel_members[channel_id] = members_in
            if members_in:
                start_times[channel_id] = time.time()
    update_live_counter.start()


@client.event
async def on_voice_state_update(member: discord.Member, before: discord.VoiceState, after: discord.VoiceState):
    if member.bot:
        return
    if before.channel and before.channel.id in MONITORED_IDS:
        ch_id = before.channel.id
        channel_members[ch_id].discard(member.id)
        if not channel_members[ch_id] and ch_id in start_times:
            elapsed = int(time.time() - start_times.pop(ch_id))
            add_session_time(ch_id, elapsed)
            await set_voice_status(ch_id, None)
    if after.channel and after.channel.id in MONITORED_IDS:
        ch_id = after.channel.id
        channel_members[ch_id].add(member.id)
        if ch_id not in start_times:
            start_times[ch_id] = time.time()


@client.event
async def on_member_join(member: discord.Member):
    if member.bot:
        return
    guild_id = member.guild.id
    now = time.time()
    recent_joins[guild_id] = [t for t in recent_joins[guild_id] if now - t < RAID_WINDOW]
    recent_joins[guild_id].append(now)
    if guild_id in raid_mode and now - raid_mode[guild_id] > RAID_COOLDOWN:
        del raid_mode[guild_id]
        recent_joins[guild_id] = []
    if len(recent_joins[guild_id]) >= RAID_THRESHOLD and guild_id not in raid_mode:
        raid_mode[guild_id] = now
        ch = member.guild.get_channel(LOG_CHANNEL_ID)
        if ch:
            raid_e = find_emoji(member.guild, "raid", "alert", "danger", "warning", "alarm", "red")
            embed = discord.Embed(
                title=f"{raid_e or '🚨'} Raid Detected!",
                description=(
                    f"{len(recent_joins[guild_id])} joins in {RAID_WINDOW}s — "
                    f"auto-banning new joiners for {RAID_COOLDOWN // 60} minutes."
                ),
                color=discord.Color.red(),
                timestamp=discord.utils.utcnow()
            )
            await ch.send(embed=embed)
    if guild_id in raid_mode:
        try:
            await member.ban(reason="Anti-raid: mass join detected")
            await log(member.guild, mod_embed("🔨 Auto-Ban (Anti-Raid)", discord.Color.red(),
                User=f"{member} ({member.id})", Reason="Anti-raid auto-ban"))
        except discord.Forbidden:
            pass


@client.event
async def on_message(message):
    if message.author.bot:
        return

    if isinstance(message.channel, discord.DMChannel):
        if message.author.id == int(os.environ["OWNER_ID"]):
            if message.reference:
                try:
                    replied_message = await message.channel.fetch_message(
                        message.reference.message_id
                    )
                    if replied_message.embeds:
                        embed = replied_message.embeds[0]
                        if embed.fields:
                            user_info = embed.fields[0].value
                            user_id = int(
                                user_info.split("(")[-1].replace(")", "")
                            )
                            user = await client.fetch_user(user_id)
                            reply_embed = discord.Embed(
                                title="📩 Message from Staff",
                                description=message.content,
                                color=discord.Color.blurple(),
                                timestamp=discord.utils.utcnow()
                            )
                            await user.send(embed=reply_embed)
                except Exception as e:
                    print(e)
            return

        owner = await client.fetch_user(int(os.environ["OWNER_ID"]))
        embed = discord.Embed(
            title="📩 New DM",
            description=message.content or "No text",
            color=discord.Color.blue()
        )
        embed.add_field(
            name="From",
            value=f"{message.author} ({message.author.id})"
        )
        await owner.send(embed=embed)
        return

    if message.author.id in afk_users:
        reason, since = afk_users.pop(message.author.id)
        elapsed = int(time.time() - since)
        mins, secs = divmod(elapsed, 60)
        wave = find_emoji(message.guild, "wave", "welcome", "hi", "hello", "back")
        await message.channel.send(
            f"{wave or '👋'} {message.author.mention} Welcome back! You were AFK for {mins}m {secs}s.",
            delete_after=8)
        await send_sticker(message.channel, message.guild, "welcome", "wave", "hi", "hello", "back")

    for mentioned in message.mentions:
        if mentioned.id in afk_users:
            reason, since = afk_users[mentioned.id]
            elapsed = int(time.time() - since)
            mins, secs = divmod(elapsed, 60)
            sleep = find_emoji(message.guild, "sleep", "zzz", "afk", "away", "moon", "bed")
            await message.channel.send(
                f"{sleep or '💤'} **{mentioned.display_name}** is currently AFK: *{reason}* ({mins}m {secs}s ago)",
                delete_after=8)

    if client.user in message.mentions:
        return await message.channel.send(f"Hey {message.author.mention}! I'm active and tracking voice rooms. Type `/help` to see what I can do! 😊")

    content = message.content
    content_lower = content.lower()
    bad_words = load_bad_words()
    smart_on = smart_filter_enabled.get(message.guild.id, True)
    caught = (
        (bad_words and any(w in content_lower for w in bad_words))
        or (smart_on and is_smart_bad(content))
    )
    if caught:
        try:
            await message.delete()
        except discord.Forbidden:
            pass
        reason = "Using inappropriate language (auto-mod)"
        count = await add_warning(message.guild, message.author, reason, "Auto-Mod")
        await dm_warning(message.author, reason, count, message.guild.name)
        return


# ─── Voice timer ──────────────────────────────────────────────────────────────

@tasks.loop(seconds=1)
async def update_live_counter():
    any_active = bool(start_times)
    for channel_id, _ in VOICE_CHANNELS:
        if channel_id in start_times:
            elapsed = int(time.time() - start_times[channel_id])
            await set_voice_status(channel_id, f"⏱️ {format_elapsed(elapsed)}")
    if any_active:
        parts = [format_elapsed(int(time.time() - start_times[cid]))
                 for cid, _ in VOICE_CHANNELS if cid in start_times]
        await client.change_presence(status=discord.Status.online,
            activity=discord.Activity(type=discord.ActivityType.watching, name=" | ".join(parts)))
    else:
        totals = [format_total(get_total_seconds(cid)) for cid, _ in VOICE_CHANNELS if get_total_seconds(cid) > 0]
        if totals:
            await client.change_presence(status=discord.Status.online,
                activity=discord.Activity(type=discord.ActivityType.watching, name="📊 " + " | ".join(totals)))
        else:
            await client.change_presence(status=discord.Status.idle,
                activity=discord.Activity(type=discord.ActivityType.watching, name="voice channels"))


# ══════════════════════════════════════════════════════════════════════════════
#  SLASH COMMANDS
# ══════════════════════════════════════════════════════════════════════════════

@tree.command(name="kick", description="Kick a member from the server")
@app_commands.default_permissions(ban_members=True)
@app_commands.describe(member="The member to kick", reason="Reason for kicking")
async def slash_kick(interaction: discord.Interaction, member: discord.Member, reason: str = "No reason provided"):
    if not has_mod_perms(interaction.user):
        return await interaction.response.send_message("❌ You don't have permission to do that.", ephemeral=True)
    try:
        try:
            dm_embed = discord.Embed(
                title="👢 You have been kicked",
                description=f"You were kicked from **{interaction.guild.name}**.",
                color=discord.Color.orange(),
                timestamp=discord.utils.utcnow()
            )
            dm_embed.add_field(name="📝 Reason", value=reason, inline=False)
            dm_embed.set_footer(text="You may rejoin with a valid invite.")
            await member.send(embed=dm_embed)
        except discord.Forbidden:
            pass
        await member.kick(reason=reason)
        e = find_emoji(interaction.guild, "kick", "boot", "bye", "door", "leave")
        await interaction.response.send_message(
            f"{e or '👢'} **{member}** has been kicked.\n📝 **{reason}**", ephemeral=True)
    except discord.Forbidden:
        await interaction.response.send_message("❌ I don't have permission to kick this member.", ephemeral=True)


@tree.command(name="ban", description="Ban a member from the server")
@app_commands.default_permissions(ban_members=True)
@app_commands.describe(member="The member to ban", reason="Reason for banning")
async def slash_ban(interaction: discord.Interaction, member: discord.Member, reason: str = "No reason provided"):
    if not has_mod_perms(interaction.user):
        return await interaction.response.send_message("❌ You don't have permission to do that.", ephemeral=True)
    try:
        try:
            dm_embed = discord.Embed(
                title="🔨 You have been banned",
                description=f"You were banned from **{interaction.guild.name}**.",
                color=discord.Color.red(),
                timestamp=discord.utils.utcnow()
            )
            dm_embed.add_field(name="📝 Reason", value=reason, inline=False)
            dm_embed.set_footer(text="Contact a moderator if you believe this was a mistake.")
            await member.send(embed=dm_embed)
        except discord.Forbidden:
            pass
        await member.ban(reason=reason)
        e = find_emoji(interaction.guild, "ban", "hammer", "banned", "angry", "red")
        await interaction.response.send_message(
            f"{e or '🔨'} **{member}** has been banned.\n📝 **{reason}**", ephemeral=True)
    except discord.Forbidden:
        await interaction.response.send_message("❌ I don't have permission to ban this member.", ephemeral=True)


@tree.command(name="unban", description="Unban a user by their ID")
@app_commands.default_permissions(ban_members=True)
@app_commands.describe(user_id="The user's ID")
async def slash_unban(interaction: discord.Interaction, user_id: str):
    if not has_mod_perms(interaction.user):
        return await interaction.response.send_message("❌ You don't have permission to do that.", ephemeral=True)
    try:
        user = await client.fetch_user(int(user_id))
        await interaction.guild.unban(user)
        await interaction.response.send_message(f"✅ **{user}** has been unbanned.", ephemeral=True)
    except Exception as e:
        await interaction.response.send_message(f"❌ Could not unban: {e}", ephemeral=True)


@tree.command(name="mute", description="Mute a member for a set duration")
@app_commands.default_permissions(ban_members=True)
@app_commands.describe(member="The member to mute", duration="Duration e.g. 10m, 2h, 1d", reason="Reason")
async def slash_mute(interaction: discord.Interaction, member: discord.Member, duration: str, reason: str = "No reason provided"):
    if not has_mod_perms(interaction.user):
        return await interaction.response.send_message("❌ You don't have permission to do that.", ephemeral=True)
    seconds = parse_duration(duration)
    if not seconds:
        return await interaction.response.send_message("❌ Invalid duration. Examples: `10m`, `2h`, `1d`", ephemeral=True)
    try:
        until = discord.utils.utcnow() + timedelta(seconds=seconds)
        await member.edit(timed_out_until=until, reason=reason)
        try:
            dm_embed = discord.Embed(
                title="🔇 You have been muted",
                description=f"You were muted in **{interaction.guild.name}** for **{duration}**.",
                color=discord.Color.orange(),
                timestamp=discord.utils.utcnow()
            )
            dm_embed.add_field(name="📝 Reason", value=reason, inline=False)
            dm_embed.set_footer(text="Please follow the server rules when the mute expires.")
            await member.send(embed=dm_embed)
        except discord.Forbidden:
            pass
        e = find_emoji(interaction.guild, "mute", "quiet", "shush", "silent")
        await interaction.response.send_message(
            f"{e or '🔇'} **{member}** has been muted for **{duration}**.\n📝 **{reason}**", ephemeral=True)
    except discord.Forbidden:
        await interaction.response.send_message("❌ I don't have permission to mute this member.", ephemeral=True)


@tree.command(name="unmute", description="Unmute a member")
@app_commands.default_permissions(ban_members=True)
@app_commands.describe(member="The member to unmute")
async def slash_unmute(interaction: discord.Interaction, member: discord.Member):
    if not has_mod_perms(interaction.user):
        return await interaction.response.send_message("❌ You don't have permission to do that.", ephemeral=True)
    try:
        await member.edit(timed_out_until=None)
        try:
            dm_embed = discord.Embed(
                title="🔊 You have been unmuted",
                description=f"Your mute in **{interaction.guild.name}** has been lifted.",
                color=discord.Color.green(),
                timestamp=discord.utils.utcnow()
            )
            dm_embed.set_footer(text="Please continue to follow the server rules.")
            await member.send(embed=dm_embed)
        except discord.Forbidden:
            pass
        e = find_emoji(interaction.guild, "free", "happy", "ok", "good", "unmute", "speak")
        await interaction.response.send_message(
            f"{e or '🔊'} **{member}** has been unmuted.", ephemeral=True)
    except discord.Forbidden:
        await interaction.response.send_message("❌ I don't have permission to unmute this member.", ephemeral=True)


@tree.command(name="warn", description="Warn a member")
@app_commands.default_permissions(ban_members=True)
@app_commands.describe(member="The member to warn", reason="Reason for the warning")
async def slash_warn(interaction: discord.Interaction, member: discord.Member, reason: str = "No reason provided"):
    if not has_mod_perms(interaction.user):
        return await interaction.response.send_message("❌ You don't have permission to do that.", ephemeral=True)
    count = await add_warning(interaction.guild, member, reason, str(interaction.user))
    await dm_warning(member, reason, count, interaction.guild.name)
    e = find_emoji(interaction.guild, "warn", "warning", "caution", "alert", "angry")
    await interaction.response.send_message(
        f"{e or '⚠️'} **{member}** has been warned. Total warnings: **{count}**\n📝 **{reason}**",
        ephemeral=True)


@tree.command(name="warnings", description="View warnings of a member")
@app_commands.default_permissions(ban_members=True)
@app_commands.describe(member="The member to check")
async def slash_warnings(interaction: discord.Interaction, member: discord.Member):
    warnings = load_json(WARNINGS_FILE)
    uid = str(member.id)
    user_warns = warnings.get(uid, [])
    if not user_warns:
        return await interaction.response.send_message(f"✅ {member.mention} has no warnings.", ephemeral=True)
    embed = discord.Embed(title=f"⚠️ Warnings — {member.display_name}",
                          color=discord.Color.yellow(), timestamp=discord.utils.utcnow())
    for i, w in enumerate(user_warns, 1):
        embed.add_field(name=f"#{i}", value=f"📝 {w['reason']}\n👮 {w['by']}", inline=False)
    await interaction.response.send_message(embed=embed, ephemeral=True)


@tree.command(name="clearwarn", description="Clear all warnings of a member")
@app_commands.default_permissions(ban_members=True)
@app_commands.describe(member="The member whose warnings to clear")
async def slash_clearwarn(interaction: discord.Interaction, member: discord.Member):
    if not has_mod_perms(interaction.user):
        return await interaction.response.send_message("❌ You don't have permission to do that.", ephemeral=True)
    warnings = load_json(WARNINGS_FILE)
    uid = str(member.id)
    count = len(warnings.get(uid, []))
    warnings[uid] = []
    save_json(WARNINGS_FILE, warnings)
    await interaction.response.send_message(
        f"✅ Cleared **{count}** warning(s) from **{member}**.", ephemeral=True)


@tree.command(name="clear", description="Delete messages from the channel")
@app_commands.default_permissions(ban_members=True)
@app_commands.describe(amount="Number of messages to delete (max 100)")
async def slash_clear(interaction: discord.Interaction, amount: int):
    if not has_mod_perms(interaction.user):
        return await interaction.response.send_message("❌ You don't have permission to do that.", ephemeral=True)
    amount = min(max(amount, 1), 100)
    await interaction.response.defer(ephemeral=True)
    deleted = await interaction.channel.purge(limit=amount)
    await interaction.followup.send(f"🗑️ Deleted **{len(deleted)}** messages.", ephemeral=True)


@tree.command(name="lock", description="Lock the current channel")
@app_commands.default_permissions(ban_members=True)
async def slash_lock(interaction: discord.Interaction):
    if not has_mod_perms(interaction.user):
        return await interaction.response.send_message("❌ You don't have permission to do that.", ephemeral=True)
    overwrite = interaction.channel.overwrites_for(interaction.guild.default_role)
    overwrite.send_messages = False
    await interaction.channel.set_permissions(interaction.guild.default_role, overwrite=overwrite)
    e = find_emoji(interaction.guild, "lock", "locked", "closed", "no")
    await interaction.response.send_message(
        f"{e or '🔒'} Channel locked. No one can send messages.", ephemeral=True)


@tree.command(name="unlock", description="Unlock the current channel")
@app_commands.default_permissions(ban_members=True)
async def slash_unlock(interaction: discord.Interaction):
    if not has_mod_perms(interaction.user):
        return await interaction.response.send_message("❌ You don't have permission to do that.", ephemeral=True)
    overwrite = interaction.channel.overwrites_for(interaction.guild.default_role)
    overwrite.send_messages = None
    await interaction.channel.set_permissions(interaction.guild.default_role, overwrite=overwrite)
    e = find_emoji(interaction.guild, "unlock", "open", "free", "green", "check")
    await interaction.response.send_message(
        f"{e or '🔓'} Channel unlocked. Everyone can send messages.", ephemeral=True)


# ─── Bad Words ────────────────────────────────────────────────────────────────

@tree.command(name="addword", description="Add a word to the bad words filter")
@app_commands.default_permissions(ban_members=True)
@app_commands.describe(word="The word to add")
async def slash_addword(interaction: discord.Interaction, word: str):
    if not has_mod_perms(interaction.user):
        return await interaction.response.send_message("❌ You don't have permission to do that.", ephemeral=True)
    word = word.lower()
    words = load_bad_words()
    if word in words:
        return await interaction.response.send_message(f"⚠️ `{word}` is already in the list.", ephemeral=True)
    words.append(word)
    save_bad_words(words)
    await interaction.response.send_message(
        f"✅ `{word}` has been added to the bad words filter.", ephemeral=True)


@tree.command(name="removeword", description="Remove a word from the bad words filter")
@app_commands.default_permissions(ban_members=True)
@app_commands.describe(word="The word to remove")
async def slash_removeword(interaction: discord.Interaction, word: str):
    if not has_mod_perms(interaction.user):
        return await interaction.response.send_message("❌ You don't have permission to do that.", ephemeral=True)
    word = word.lower()
    words = load_bad_words()
    if word not in words:
        return await interaction.response.send_message(f"❌ `{word}` is not in the list.", ephemeral=True)
    words.remove(word)
    save_bad_words(words)
    await interaction.response.send_message(
        f"✅ `{word}` has been removed from the filter.", ephemeral=True)


@tree.command(name="badwords", description="Show the bad words list")
@app_commands.default_permissions(ban_members=True)
async def slash_badwords(interaction: discord.Interaction):
    if not has_mod_perms(interaction.user):
        return await interaction.response.send_message("❌ You don't have permission to do that.", ephemeral=True)
    words = load_bad_words()
    if not words:
        return await interaction.response.send_message("📋 The bad words list is empty.", ephemeral=True)
    formatted = " • ".join(f"`{w}`" for w in words)
    embed = discord.Embed(title=f"📋 Bad Words List ({len(words)})", description=formatted,
                          color=discord.Color.orange(), timestamp=discord.utils.utcnow())
    await interaction.response.send_message(embed=embed, ephemeral=True)


@tree.command(name="smartfilter", description="Toggle the smart bad word filter on or off")
@app_commands.default_permissions(ban_members=True)
@app_commands.describe(state="on or off")
@app_commands.choices(state=[
    app_commands.Choice(name="on", value="on"),
    app_commands.Choice(name="off", value="off"),
])
async def slash_smartfilter(interaction: discord.Interaction, state: str):
    if not has_mod_perms(interaction.user):
        return await interaction.response.send_message("❌ You don't have permission to do that.", ephemeral=True)
    enabled = state == "on"
    smart_filter_enabled[interaction.guild.id] = enabled
    if enabled:
        await interaction.response.send_message("🧠 Smart filter is now **ON** — automatically detecting bad words in English and Egyptian Arabic.", ephemeral=True)
    else:
        await interaction.response.send_message("⛔ Smart filter is now **OFF** — only the manual `/addword` list will be used.", ephemeral=True)


@tree.command(name="filtertest", description="Test if a word or phrase would be caught by the filter")
@app_commands.default_permissions(ban_members=True)
@app_commands.describe(text="The word or phrase to test")
async def slash_filtertest(interaction: discord.Interaction, text: str):
    if not has_mod_perms(interaction.user):
        return await interaction.response.send_message("❌ You don't have permission to do that.", ephemeral=True)
    bad_words = load_bad_words()
    content_lower = text.lower()
    hit_manual = bad_words and any(w in content_lower for w in bad_words)
    hit_smart = is_smart_bad(text)
    smart_on = smart_filter_enabled.get(interaction.guild.id, True)
    would_catch = hit_manual or (smart_on and hit_smart)
    embed = discord.Embed(
        title="🔍 Filter Test Result",
        description=f"**Input:** `{text}`",
        color=discord.Color.red() if would_catch else discord.Color.green(),
        timestamp=discord.utils.utcnow()
    )
    embed.add_field(name="📋 Manual list", value="✅ Caught" if hit_manual else "❌ Not caught", inline=True)
    embed.add_field(name="🧠 Smart filter", value=("✅ Caught" if hit_smart else "❌ Not caught") + ("" if smart_on else " *(disabled)*"), inline=True)
    embed.add_field(name="⚡ Final verdict", value="🚫 **Would be deleted**" if would_catch else "✅ **Would pass**", inline=False)
    await interaction.response.send_message(embed=embed, ephemeral=True)


@tree.command(name="modlog", description="View recent mod actions and member warning counts")
@app_commands.default_permissions(ban_members=True)
@app_commands.describe(member="Show full warning history for a specific member (optional)")
async def slash_modlog(interaction: discord.Interaction, member: discord.Member = None):
    if not has_mod_perms(interaction.user):
        return await interaction.response.send_message("❌ You don't have permission to do that.", ephemeral=True)

    warnings_data = load_json(WARNINGS_FILE)

    if member:
        uid = str(member.id)
        user_warns = warnings_data.get(uid, [])
        count = len(user_warns)
        if not user_warns:
            return await interaction.response.send_message(
                f"✅ **{member.display_name}** has no warnings on record.", ephemeral=True)
        embed = discord.Embed(
            title=f"📋 Warning History — {member.display_name}",
            description=f"**{member}** • {member.mention}\nTotal warnings: **{count}**",
            color=discord.Color.red() if count >= 5 else discord.Color.orange() if count >= 3 else discord.Color.yellow(),
            timestamp=discord.utils.utcnow()
        )
        embed.set_thumbnail(url=member.display_avatar.url)
        for i, w in enumerate(reversed(user_warns[-10:]), 1):
            ts = int(w.get("time", 0))
            when = f"<t:{ts}:R>" if ts else "Unknown"
            embed.add_field(
                name=f"#{count - i + 1} — {when}",
                value=f"📝 {w['reason']}\n👮 by {w['by']}",
                inline=False
            )
        if count > 10:
            embed.set_footer(text=f"Showing last 10 of {count} warnings.")
        await interaction.response.send_message(embed=embed, ephemeral=True)
        return

    all_entries = []
    for uid, warns in warnings_data.items():
        for w in warns:
            all_entries.append((uid, len(warns), w))
    all_entries.sort(key=lambda x: x[2].get("time", 0), reverse=True)
    recent = all_entries[:15]

    if not recent:
        return await interaction.response.send_message("📋 No mod actions on record yet.", ephemeral=True)

    embed = discord.Embed(
        title="🛡️ Recent Mod Actions",
        color=discord.Color.blurple(),
        timestamp=discord.utils.utcnow()
    )

    top_offenders = {}
    for uid, total, _ in all_entries:
        top_offenders[uid] = total
    top_sorted = sorted(top_offenders.items(), key=lambda x: x[1], reverse=True)[:5]
    leaderboard = []
    for uid, total in top_sorted:
        user = interaction.guild.get_member(int(uid))
        name = user.display_name if user else f"User {uid}"
        leaderboard.append(f"**{name}** — {total} warning{'s' if total != 1 else ''}")
    embed.add_field(name="⚠️ Most Warned Members", value="\n".join(leaderboard) or "None", inline=False)

    lines = []
    for uid, total, w in recent:
        user = interaction.guild.get_member(int(uid))
        name = user.display_name if user else f"User {uid}"
        ts = int(w.get("time", 0))
        when = f"<t:{ts}:R>" if ts else "Unknown"
        lines.append(f"{when} **{name}** (⚠️{total}) — {w['reason'][:50]} • *by {w['by']}*")
    embed.add_field(name="📜 Last 15 Actions", value="\n".join(lines), inline=False)
    embed.set_footer(text="Use /modlog @member for full history of a specific member.")
    await interaction.response.send_message(embed=embed, ephemeral=True)


@tree.command(name="mutedlist", description="Show all currently muted/timed-out members and when their mute expires")
@app_commands.default_permissions(ban_members=True)
async def slash_mutedlist(interaction: discord.Interaction):
    if not has_mod_perms(interaction.user):
        return await interaction.response.send_message("❌ You don't have permission to do that.", ephemeral=True)

    await interaction.response.defer(ephemeral=True)

    now = discord.utils.utcnow()
    muted = [
        m for m in interaction.guild.members
        if m.timed_out_until and m.timed_out_until > now
    ]

    if not muted:
        return await interaction.followup.send("✅ No members are currently muted.", ephemeral=True)

    muted.sort(key=lambda m: m.timed_out_until)

    warnings_data = load_json(WARNINGS_FILE)

    embed = discord.Embed(
        title=f"🔇 Currently Muted Members ({len(muted)})",
        color=discord.Color.orange(),
        timestamp=now
    )

    for m in muted:
        uid = str(m.id)
        warn_count = len(warnings_data.get(uid, []))
        expires_ts = int(m.timed_out_until.timestamp())
        embed.add_field(
            name=f"{m.display_name}",
            value=(
                f"👤 {m.mention}\n"
                f"⏰ Expires: <t:{expires_ts}:R> (<t:{expires_ts}:f>)\n"
                f"⚠️ Total warnings: **{warn_count}**"
            ),
            inline=False
        )

    embed.set_footer(text="Use /unmute @member to lift a mute early.")
    await interaction.followup.send(embed=embed, ephemeral=True)


# ─── Info ─────────────────────────────────────────────────────────────────────

@tree.command(name="ping", description="Check the bot's latency")
async def slash_ping(interaction: discord.Interaction):
    await interaction.response.send_message(f"🏓 Pong! `{round(client.latency * 1000)}ms`")


@tree.command(name="serverinfo", description="Show server information")
async def slash_serverinfo(interaction: discord.Interaction):
    g = interaction.guild
    embed = discord.Embed(title=f"🏠 {g.name}", color=discord.Color.blurple(), timestamp=discord.utils.utcnow())
    if g.icon:
        embed.set_thumbnail(url=g.icon.url)
    embed.add_field(name="👑 Owner", value=str(g.owner), inline=True)
    embed.add_field(name="👥 Members", value=str(g.member_count), inline=True)
    embed.add_field(name="💬 Channels", value=str(len(g.channels)), inline=True)
    embed.add_field(name="🎭 Roles", value=str(len(g.roles)), inline=True)
    embed.add_field(name="🌍 Locale", value=str(g.preferred_locale), inline=True)
    embed.add_field(name="📅 Created", value=g.created_at.strftime("%d/%m/%Y"), inline=True)
    embed.set_footer(text=f"ID: {g.id}")
    await interaction.response.send_message(embed=embed, view=DismissView(interaction.user.id))


@tree.command(name="userinfo", description="Show information about a user")
@app_commands.describe(member="The member to check (leave empty for yourself)")
async def slash_userinfo(interaction: discord.Interaction, member: discord.Member = None):
    member = member or interaction.user
    embed = discord.Embed(title=f"👤 {member}", color=getattr(member, "color", discord.Color.blurple()),
                          timestamp=discord.utils.utcnow())
    embed.set_thumbnail(url=member.display_avatar.url)
    embed.add_field(name="🪪 ID", value=str(member.id), inline=True)
    embed.add_field(name="📅 Joined Discord", value=member.created_at.strftime("%d/%m/%Y"), inline=True)
    if hasattr(member, "joined_at") and member.joined_at:
        embed.add_field(name="🏠 Joined Server", value=member.joined_at.strftime("%d/%m/%Y"), inline=True)
    roles = [r.mention for r in getattr(member, "roles", [])[1:]]
    embed.add_field(name=f"🎭 Roles ({len(roles)})", value=" ".join(roles) if roles else "None", inline=False)
    await interaction.response.send_message(embed=embed, view=DismissView(interaction.user.id))


@tree.command(name="avatar", description="Show a user's profile picture")
@app_commands.describe(member="The member (leave empty for yourself)")
async def slash_avatar(interaction: discord.Interaction, member: discord.Member = None):
    member = member or interaction.user
    embed = discord.Embed(title=f"🖼️ {member.display_name}'s Avatar", color=discord.Color.blurple())
    embed.set_image(url=member.display_avatar.url)
    embed.add_field(name="⬇️ Download",
        value=f"[PNG]({member.display_avatar.with_format('png').url}) | [JPG]({member.display_avatar.with_format('jpeg').url})")
    await interaction.response.send_message(embed=embed, view=DismissView(interaction.user.id))


@tree.command(name="roleinfo", description="Show information about a role")
@app_commands.describe(role="The role to check")
async def slash_roleinfo(interaction: discord.Interaction, role: discord.Role):
    embed = discord.Embed(title=f"🎭 {role.name}", color=role.color, timestamp=discord.utils.utcnow())
    embed.add_field(name="🪪 ID", value=str(role.id), inline=True)
    embed.add_field(name="👥 Members", value=str(len(role.members)), inline=True)
    embed.add_field(name="🎨 Color", value=str(role.color), inline=True)
    embed.add_field(name="📌 Hoisted", value="✅" if role.hoist else "❌", inline=True)
    embed.add_field(name="🤖 Managed", value="✅" if role.managed else "❌", inline=True)
    embed.add_field(name="📅 Created", value=role.created_at.strftime("%d/%m/%Y"), inline=True)
    await interaction.response.send_message(embed=embed, view=DismissView(interaction.user.id))


# ─── Utility ──────────────────────────────────────────────────────────────────

@tree.command(name="poll", description="Create a poll with reactions")
@app_commands.describe(
    question="The poll question",
    option1="Option 1", option2="Option 2",
    option3="Option 3 (optional)", option4="Option 4 (optional)", option5="Option 5 (optional)",
)
async def slash_poll(interaction: discord.Interaction, question: str,
                     option1: str, option2: str,
                     option3: str = None, option4: str = None, option5: str = None):
    options = [o for o in [option1, option2, option3, option4, option5] if o]
    emojis = ["1️⃣", "2️⃣", "3️⃣", "4️⃣", "5️⃣"]
    desc = "\n".join(f"{emojis[i]} {opt}" for i, opt in enumerate(options))
    embed = discord.Embed(title=f"📊 {question}", description=desc,
                          color=discord.Color.blurple(), timestamp=discord.utils.utcnow())
    embed.set_footer(text=f"Poll by {interaction.user.display_name}")
    await interaction.response.send_message(embed=embed, view=PollView(interaction.user.id))
    poll_msg = await interaction.original_response()
    for i in range(len(options)):
        await poll_msg.add_reaction(emojis[i])


@tree.command(name="announce", description="Send an official announcement")
@app_commands.default_permissions(ban_members=True)
@app_commands.describe(message="The announcement text")
async def slash_announce(interaction: discord.Interaction, message: str):
    if not has_mod_perms(interaction.user):
        return await interaction.response.send_message("❌ You don't have permission to do that.", ephemeral=True)
    embed = discord.Embed(description=message, color=discord.Color.red(), timestamp=discord.utils.utcnow())
    embed.set_author(name=interaction.user.display_name, icon_url=interaction.user.display_avatar.url)
    embed.set_footer(text=interaction.guild.name)
    await interaction.response.send_message("@here", embed=embed)


@tree.command(name="embed", description="Send a custom embed message")
@app_commands.default_permissions(ban_members=True)
@app_commands.describe(message="The message content", title="Optional title")
async def slash_embed(interaction: discord.Interaction, message: str, title: str = None):
    if not has_mod_perms(interaction.user):
        return await interaction.response.send_message("❌ You don't have permission to do that.", ephemeral=True)
    embed = discord.Embed(title=title, description=message,
                          color=discord.Color.blurple(), timestamp=discord.utils.utcnow())
    await interaction.response.send_message(embed=embed)


@tree.command(name="afk", description="Set your AFK status")
@app_commands.describe(reason="Reason for being AFK (optional)")
async def slash_afk(interaction: discord.Interaction, reason: str = "Away"):
    afk_users[interaction.user.id] = (reason, time.time())
    e = find_emoji(interaction.guild, "sleep", "zzz", "afk", "away", "moon", "bed", "night")
    await interaction.response.send_message(
        f"{e or '💤'} {interaction.user.mention} is now AFK: *{reason}*")


@tree.command(name="remind", description="Set a reminder")
@app_commands.describe(duration="Duration e.g. 10m, 2h, 1d", message="What to remind you about")
async def slash_remind(interaction: discord.Interaction, duration: str, message: str):
    seconds = parse_duration(duration)
    if not seconds:
        return await interaction.response.send_message(
            "❌ Invalid duration. Examples: `10m`, `2h`, `30s`", ephemeral=True)
    if seconds > 86400:
        return await interaction.response.send_message("❌ Maximum reminder duration is 1 day.", ephemeral=True)
    await interaction.response.send_message(
        f"⏰ Got it! I'll remind you about **{message}** in **{duration}**.", ephemeral=True)

    async def send_reminder():
        await asyncio.sleep(seconds)
        await interaction.channel.send(f"⏰ {interaction.user.mention} Reminder: **{message}**")

    asyncio.create_task(send_reminder())


# ─── Help ─────────────────────────────────────────────────────────────────────

# ─── Voice Channel Moderation ─────────────────────────────────────────────────

@tree.command(name="vcjoin", description="Make the bot join a voice channel")
@app_commands.default_permissions(ban_members=True)
@app_commands.describe(channel="The voice channel to join (defaults to your current VC)")
async def slash_vcjoin(interaction: discord.Interaction, channel: discord.VoiceChannel = None):
    if not has_mod_perms(interaction.user):
        return await interaction.response.send_message("❌ You don't have permission to do that.", ephemeral=True)
    target = channel or (interaction.user.voice.channel if interaction.user.voice else None)
    if not target:
        return await interaction.response.send_message("❌ You're not in a voice channel and no channel was specified.", ephemeral=True)
    guild_id = interaction.guild.id
    existing = vc_clients.get(guild_id)
    if existing and existing.is_connected():
        await existing.move_to(target)
    else:
        try:
            vc = await target.connect()
            vc_clients[guild_id] = vc
        except discord.ClientException:
            return await interaction.response.send_message("❌ Already connected somewhere — use `/vcleave` first.", ephemeral=True)
    await interaction.response.send_message(f"✅ Joined **{target.name}**.", ephemeral=True)


@tree.command(name="vcleave", description="Make the bot leave its current voice channel")
@app_commands.default_permissions(ban_members=True)
async def slash_vcleave(interaction: discord.Interaction):
    if not has_mod_perms(interaction.user):
        return await interaction.response.send_message("❌ You don't have permission to do that.", ephemeral=True)
    guild_id = interaction.guild.id
    vc = vc_clients.pop(guild_id, None)
    if vc and vc.is_connected():
        await vc.disconnect()
        await interaction.response.send_message("✅ Left the voice channel.", ephemeral=True)
    else:
        await interaction.response.send_message("❌ I'm not in a voice channel.", ephemeral=True)


@tree.command(name="vcmute", description="Server-mute a member in voice chat")
@app_commands.default_permissions(ban_members=True)
@app_commands.describe(member="The member to mute", reason="Reason")
async def slash_vcmute(interaction: discord.Interaction, member: discord.Member, reason: str = "No reason provided"):
    if not has_mod_perms(interaction.user):
        return await interaction.response.send_message("❌ You don't have permission to do that.", ephemeral=True)
    if not member.voice:
        return await interaction.response.send_message(f"❌ **{member}** is not in a voice channel.", ephemeral=True)
    try:
        await member.edit(mute=True, reason=reason)
        await interaction.response.send_message(f"🔇 **{member}** has been server-muted.\n📝 {reason}", ephemeral=True)
    except discord.Forbidden:
        await interaction.response.send_message("❌ I don't have permission to mute that member.", ephemeral=True)


@tree.command(name="vcunmute", description="Remove server-mute from a member in voice chat")
@app_commands.default_permissions(ban_members=True)
@app_commands.describe(member="The member to unmute")
async def slash_vcunmute(interaction: discord.Interaction, member: discord.Member):
    if not has_mod_perms(interaction.user):
        return await interaction.response.send_message("❌ You don't have permission to do that.", ephemeral=True)
    if not member.voice:
        return await interaction.response.send_message(f"❌ **{member}** is not in a voice channel.", ephemeral=True)
    try:
        await member.edit(mute=False)
        await interaction.response.send_message(f"🔊 **{member}** has been unmuted in voice.", ephemeral=True)
    except discord.Forbidden:
        await interaction.response.send_message("❌ I don't have permission to unmute that member.", ephemeral=True)


@tree.command(name="vcdeafen", description="Server-deafen a member in voice chat")
@app_commands.default_permissions(ban_members=True)
@app_commands.describe(member="The member to deafen", reason="Reason")
async def slash_vcdeafen(interaction: discord.Interaction, member: discord.Member, reason: str = "No reason provided"):
    if not has_mod_perms(interaction.user):
        return await interaction.response.send_message("❌ You don't have permission to do that.", ephemeral=True)
    if not member.voice:
        return await interaction.response.send_message(f"❌ **{member}** is not in a voice channel.", ephemeral=True)
    try:
        await member.edit(deafen=True, reason=reason)
        await interaction.response.send_message(f"🔕 **{member}** has been server-deafened.\n📝 {reason}", ephemeral=True)
    except discord.Forbidden:
        await interaction.response.send_message("❌ I don't have permission to deafen that member.", ephemeral=True)


@tree.command(name="vcundeafen", description="Remove server-deafen from a member in voice chat")
@app_commands.default_permissions(ban_members=True)
@app_commands.describe(member="The member to undeafen")
async def slash_vcundeafen(interaction: discord.Interaction, member: discord.Member):
    if not has_mod_perms(interaction.user):
        return await interaction.response.send_message("❌ You don't have permission to do that.", ephemeral=True)
    if not member.voice:
        return await interaction.response.send_message(f"❌ **{member}** is not in a voice channel.", ephemeral=True)
    try:
        await member.edit(deafen=False)
        await interaction.response.send_message(f"🔔 **{member}** has been undeafened.", ephemeral=True)
    except discord.Forbidden:
        await interaction.response.send_message("❌ I don't have permission to undeafen that member.", ephemeral=True)


@tree.command(name="vckick", description="Disconnect a member from their voice channel")
@app_commands.default_permissions(ban_members=True)
@app_commands.describe(member="The member to disconnect", reason="Reason")
async def slash_vckick(interaction: discord.Interaction, member: discord.Member, reason: str = "No reason provided"):
    if not has_mod_perms(interaction.user):
        return await interaction.response.send_message("❌ You don't have permission to do that.", ephemeral=True)
    if not member.voice:
        return await interaction.response.send_message(f"❌ **{member}** is not in a voice channel.", ephemeral=True)
    try:
        await member.move_to(None, reason=reason)
        await interaction.response.send_message(f"👢 **{member}** has been disconnected from voice.\n📝 {reason}", ephemeral=True)
    except discord.Forbidden:
        await interaction.response.send_message("❌ I don't have permission to disconnect that member.", ephemeral=True)


@tree.command(name="vcmove", description="Move a member to a different voice channel")
@app_commands.default_permissions(ban_members=True)
@app_commands.describe(member="The member to move", channel="The destination voice channel")
async def slash_vcmove(interaction: discord.Interaction, member: discord.Member, channel: discord.VoiceChannel):
    if not has_mod_perms(interaction.user):
        return await interaction.response.send_message("❌ You don't have permission to do that.", ephemeral=True)
    if not member.voice:
        return await interaction.response.send_message(f"❌ **{member}** is not in a voice channel.", ephemeral=True)
    try:
        await member.move_to(channel)
        await interaction.response.send_message(f"➡️ **{member}** has been moved to **{channel.name}**.", ephemeral=True)
    except discord.Forbidden:
        await interaction.response.send_message("❌ I don't have permission to move that member.", ephemeral=True)


@tree.command(name="vcmuteall", description="Server-mute everyone in your current voice channel")
@app_commands.default_permissions(ban_members=True)
@app_commands.describe(channel="The voice channel to mute (defaults to your current VC)")
async def slash_vcmuteall(interaction: discord.Interaction, channel: discord.VoiceChannel = None):
    if not has_mod_perms(interaction.user):
        return await interaction.response.send_message("❌ You don't have permission to do that.", ephemeral=True)
    target = channel or (interaction.user.voice.channel if interaction.user.voice else None)
    if not target:
        return await interaction.response.send_message("❌ No channel specified and you're not in a voice channel.", ephemeral=True)
    await interaction.response.defer(ephemeral=True)
    count = 0
    for member in target.members:
        if not member.bot and not member.voice.mute:
            try:
                await member.edit(mute=True)
                count += 1
            except discord.Forbidden:
                pass
    await interaction.followup.send(f"🔇 Muted **{count}** member(s) in **{target.name}**.", ephemeral=True)


@tree.command(name="vcunmuteall", description="Remove server-mute from everyone in a voice channel")
@app_commands.default_permissions(ban_members=True)
@app_commands.describe(channel="The voice channel (defaults to your current VC)")
async def slash_vcunmuteall(interaction: discord.Interaction, channel: discord.VoiceChannel = None):
    if not has_mod_perms(interaction.user):
        return await interaction.response.send_message("❌ You don't have permission to do that.", ephemeral=True)
    target = channel or (interaction.user.voice.channel if interaction.user.voice else None)
    if not target:
        return await interaction.response.send_message("❌ No channel specified and you're not in a voice channel.", ephemeral=True)
    await interaction.response.defer(ephemeral=True)
    count = 0
    for member in target.members:
        if not member.bot and member.voice.mute:
            try:
                await member.edit(mute=False)
                count += 1
            except discord.Forbidden:
                pass
    await interaction.followup.send(f"🔊 Unmuted **{count}** member(s) in **{target.name}**.", ephemeral=True)


@tree.command(name="help", description="Show all available commands")
async def slash_help(interaction: discord.Interaction):
    embed = discord.Embed(title="📋 Bot Commands", color=discord.Color.blurple(), timestamp=discord.utils.utcnow())
    embed.add_field(name="🔨 Moderation 🔒", value=(
        "`/kick` `/ban` `/unban`\n`/mute` `/unmute`\n`/warn` `/warnings` `/clearwarn`\n`/clear` `/lock` `/unlock`"
    ), inline=False)
    embed.add_field(name="🎤 Voice Mod 🔒", value=(
        "`/vcjoin` `/vcleave`\n"
        "`/vcmute` `/vcunmute`\n"
        "`/vcdeafen` `/vcundeafen`\n"
        "`/vckick` `/vcmove`\n"
        "`/vcmuteall` `/vcunmuteall`"
    ), inline=False)
    embed.add_field(name="🚫 Filter 🔒", value="`/addword` `/removeword` `/badwords`\n`/smartfilter` `/filtertest`", inline=False)
    embed.add_field(name="📋 Mod Logs 🔒", value="`/modlog` `/mutedlist`", inline=False)
    embed.add_field(name="ℹ️ Info", value="`/ping` `/serverinfo` `/userinfo` `/avatar` `/roleinfo`", inline=False)
    embed.add_field(name="🛠️ Utility", value="`/poll` `/announce` `/embed` `/afk` `/remind`", inline=False)
    embed.set_footer(text="🔒 = Mods only | Everything else is for everyone")
    await interaction.response.send_message(embed=embed, view=DismissView(interaction.user.id))


# ─── Run ──────────────────────────────────────────────────────────────────────
client.run(TOKEN)

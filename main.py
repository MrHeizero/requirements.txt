import discord
import os

intents = discord.Intents.default()
client = discord.Client(intents=intents)

@client.event
async def on_ready():
    print(f'{client.user} has connected to Discord!')

# Set DISCORD_TOKEN in Railway service variables
client.run(os.environ['DISCORD_TOKEN'])

"""Call gate2_sync on the tree Gate 2 daemon and print its report."""
import asyncio
import sys
import time

from mcp import ClientSession
from mcp.client.sse import sse_client

URL = sys.argv[1] if len(sys.argv) > 1 else "http://127.0.0.1:7872/sse"


async def main():
    async with sse_client(URL, timeout=30, sse_read_timeout=4 * 3600) as (r, w):
        async with ClientSession(r, w) as s:
            await s.initialize()
            tools = await s.list_tools()
            print("tools:", [t.name for t in tools.tools])
            t0 = time.time()
            res = await s.call_tool("gate2_sync", {"pull": True, "fetch_cache": True})
            print(f"gate2_sync in {time.time() - t0:.1f}s:\n{res.content[0].text}")


asyncio.run(main())

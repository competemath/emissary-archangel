"""Prove the local Leak I (loogle + moogle on the Tengoku tree) answers.
Usage: python leak-i-test.py [sse_url]. Exit 0 and print LEAK_I_OK only when
loogle_search returns real hits from the tree."""
import asyncio
import sys
import time

from mcp import ClientSession
from mcp.client.sse import sse_client

URL = sys.argv[1] if len(sys.argv) > 1 else "http://127.0.0.1:7874/sse"


async def main():
    async with sse_client(URL, timeout=30, sse_read_timeout=30 * 60) as (r, w):
        async with ClientSession(r, w) as s:
            await s.initialize()
            tools = [t.name for t in (await s.list_tools()).tools]
            print("tools:", tools)
            t0 = time.time()
            res = await s.call_tool("loogle_search", {"query": "Nat.add_comm"})
            text = res.content[0].text if res.content else ""
            dt = time.time() - t0
            ok = "Nat.add_comm" in text and "error" not in text.lower()[:200]
            print(f"[{'OK ' if ok else 'BAD'}] loogle_search Nat.add_comm in {dt:.0f}s — {' '.join(text.split())[:300]}")
            res2 = await s.call_tool("moogle_search", {"concept": "commutativity of natural number addition"})
            text2 = res2.content[0].text if res2.content else ""
            ok2 = bool(text2.strip()) and "error" not in text2.lower()[:200]
            print(f"[{'OK ' if ok2 else 'BAD'}] moogle_search — {' '.join(text2.split())[:200]}")
            print("LEAK_I_OK" if ok and ok2 else "LEAK_I_FAILED")
            sys.exit(0 if ok and ok2 else 1)


asyncio.run(main())

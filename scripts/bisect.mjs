// The halving of a failed batch (setup-source.mjs: the closure and export phases), on its own so that it can be tested over real module lists.
// `runBatch(items)` says whether the whole batch went through (true) or failed (false); `runOne(item)` handles one item and its own failure.
// A batch that fails is split in two and each half is tried, down to single items, so that a batch killed for memory or time costs a few smaller processes, not one per item
// (flt-anthropic, 3 Nov 2026: one batch of 471 killed at once sent the shard down 471 single imports of ~11 GB each, past its 5 hours, for 129 files).
// `onSplit(size, firstHalf)` is told of each split (for the log).
export async function bisectItems(items, runBatch, runOne, onSplit = () => {}) {
  if (items.length === 1) return runOne(items[0])
  if (await runBatch(items)) return
  const half = Math.ceil(items.length / 2)
  onSplit(items.length, half)
  await bisectItems(items.slice(0, half), runBatch, runOne, onSplit)
  await bisectItems(items.slice(half), runBatch, runOne, onSplit)
}

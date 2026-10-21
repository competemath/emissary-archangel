// One line of the translation ledger (data/translate/<key>.jsonl) from an `entry-result` frame of the bridge.
//
// Besides the outcome, a row says WHY, with the text behind it, so that what each mechanism catches can be measured later (how often
// Gate 2 refuses a script that compiles, for which reason, what its first differences said). Fields, all optional but `outcome`:
//   reason          a short code: a Gate 2 reason (name_collision, kernel_error, old_name_not_in_export, ...), or compile_error,
//                   lint_refused, content_lint, known_collision, leak_clash, prefix_known_broken, infra_blocked, export_unavailable,
//                   agent_banked, agent_unavailable, agent_gave_up, unexpected_error
//   detail          the text behind it: the GATE2_FAIL block, the first compile error, the lint reasons (at most 900 characters)
//   names           the declarations involved (at most 8)
//   gate2Rejections for an entry the agent worked on: the Gate 2 refusals it met on the way (at most 3, with their text)
// Rows written before this existed carry only the outcome.
const cut = (s, n) => String(s == null ? "" : s).replace(/\s+/g, " ").trim().slice(0, n)

export function ledgerRow(o, at = new Date().toISOString()) {
  const row = { id: o.id, name: o.name, sourcePath: o.sourcePath, outcome: o.outcome, at }
  if (o.error) row.error = cut(o.error, 300)
  if (o.reason) row.reason = cut(o.reason, 60)
  if (o.detail) row.detail = cut(o.detail, 900)
  if (Array.isArray(o.names) && o.names.length) row.names = o.names.slice(0, 8).map((n) => cut(n, 120))
  if (Array.isArray(o.gate2Rejections) && o.gate2Rejections.length) row.gate2Rejections = o.gate2Rejections.slice(0, 3).map((g) => ({ reason: cut(g?.reason, 60), detail: cut(g?.detail, 400) }))
  return row
}

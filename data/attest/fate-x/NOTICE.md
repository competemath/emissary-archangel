# FATE-X statements

`translated.json` holds the 100 FATE-X problem statements (`FATEX/1.lean` .. `FATEX/100.lean` of
https://github.com/frenzymath/FATE-X at commit `a6fb49ee85fd05bb8ce9fc66e1c66797b5a0592d`, v1.2.0) as they were
made to compile on Lean v4.34.0-rc2 against the Tengoku tree: the `import Mathlib` line and the doc comments are
removed, and for the nine problems with a `port` field a name or a modifier was changed (the field says what and
why). The proofs are `sorry`: these are statements.

The upstream text is MIT-licensed, Copyright (c) 2025 FrenzyMath. The licence and copyright notice of the upstream
repository apply to this file:

> Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated
> documentation files (the "Software"), to deal in the Software without restriction, including without limitation the
> rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit
> persons to whom the Software is furnished to do so, subject to the following conditions: The above copyright notice
> and this permission notice shall be included in all copies or substantial portions of the Software.

Nothing here is, or can become, a Tengoku record: see the header of `.github/workflows/attest-statements.yml`.

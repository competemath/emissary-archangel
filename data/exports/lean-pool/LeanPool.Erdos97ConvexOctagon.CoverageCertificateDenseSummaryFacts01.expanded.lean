/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.Erdos97ConvexOctagon.CoverageCertificateDenseSummarySoundness


-- @@ L10-10 verbatim
/-! # Canonical audits for dense certificate summaries -/


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage


-- @@ L16-19 verbatim
/-- Dense pattern summary group 5 agrees with canonical audited data. -/
theorem densePatternSummaries05_canonical :
    densePatternSummaries05.toList.all patternSummaryCanonicalB = true := by
  decide


-- @@ L21-24 verbatim
/-- Dense pattern summary group 6 agrees with canonical audited data. -/
theorem densePatternSummaries06_canonical :
    densePatternSummaries06.toList.all patternSummaryCanonicalB = true := by
  decide


-- @@ L26-29 verbatim
/-- Dense pattern summary group 7 agrees with canonical audited data. -/
theorem densePatternSummaries07_canonical :
    densePatternSummaries07.toList.all patternSummaryCanonicalB = true := by
  decide


-- @@ L31-34 verbatim
/-- Dense pattern summary group 8 agrees with canonical audited data. -/
theorem densePatternSummaries08_canonical :
    densePatternSummaries08.toList.all patternSummaryCanonicalB = true := by
  decide


-- @@ L36-39 verbatim
/-- Dense pattern summary group 9 agrees with canonical audited data. -/
theorem densePatternSummaries09_canonical :
    densePatternSummaries09.toList.all patternSummaryCanonicalB = true := by
  decide


-- @@ L41-41 verbatim
end Erdos97Octagon.RawIncidence.StaticDirectCoverage

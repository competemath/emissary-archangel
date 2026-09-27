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
/-- Dense pattern summary group 15 agrees with canonical audited data. -/
theorem densePatternSummaries15_canonical :
    densePatternSummaries15.toList.all patternSummaryCanonicalB = true := by
  decide


-- @@ L21-24 verbatim
/-- Dense pattern summary group 16 agrees with canonical audited data. -/
theorem densePatternSummaries16_canonical :
    densePatternSummaries16.toList.all patternSummaryCanonicalB = true := by
  decide


-- @@ L26-29 verbatim
/-- Dense pattern summary group 17 agrees with canonical audited data. -/
theorem densePatternSummaries17_canonical :
    densePatternSummaries17.toList.all patternSummaryCanonicalB = true := by
  decide


-- @@ L31-34 verbatim
/-- Dense pattern summary group 18 agrees with canonical audited data. -/
theorem densePatternSummaries18_canonical :
    densePatternSummaries18.toList.all patternSummaryCanonicalB = true := by
  decide


-- @@ L36-39 verbatim
/-- Dense pattern summary group 19 agrees with canonical audited data. -/
theorem densePatternSummaries19_canonical :
    densePatternSummaries19.toList.all patternSummaryCanonicalB = true := by
  decide


-- @@ L41-41 verbatim
end Erdos97Octagon.RawIncidence.StaticDirectCoverage

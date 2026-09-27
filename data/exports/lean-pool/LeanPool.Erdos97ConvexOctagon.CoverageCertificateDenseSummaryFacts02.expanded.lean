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
/-- Dense pattern summary group 10 agrees with canonical audited data. -/
theorem densePatternSummaries10_canonical :
    densePatternSummaries10.toList.all patternSummaryCanonicalB = true := by
  decide


-- @@ L21-24 verbatim
/-- Dense pattern summary group 11 agrees with canonical audited data. -/
theorem densePatternSummaries11_canonical :
    densePatternSummaries11.toList.all patternSummaryCanonicalB = true := by
  decide


-- @@ L26-29 verbatim
/-- Dense pattern summary group 12 agrees with canonical audited data. -/
theorem densePatternSummaries12_canonical :
    densePatternSummaries12.toList.all patternSummaryCanonicalB = true := by
  decide


-- @@ L31-34 verbatim
/-- Dense pattern summary group 13 agrees with canonical audited data. -/
theorem densePatternSummaries13_canonical :
    densePatternSummaries13.toList.all patternSummaryCanonicalB = true := by
  decide


-- @@ L36-39 verbatim
/-- Dense pattern summary group 14 agrees with canonical audited data. -/
theorem densePatternSummaries14_canonical :
    densePatternSummaries14.toList.all patternSummaryCanonicalB = true := by
  decide


-- @@ L41-41 verbatim
end Erdos97Octagon.RawIncidence.StaticDirectCoverage

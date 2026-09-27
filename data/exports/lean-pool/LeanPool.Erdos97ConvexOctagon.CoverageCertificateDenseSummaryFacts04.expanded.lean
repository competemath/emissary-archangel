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
/-- Dense pattern summary group 20 agrees with canonical audited data. -/
theorem densePatternSummaries20_canonical :
    densePatternSummaries20.toList.all patternSummaryCanonicalB = true := by
  decide


-- @@ L21-24 verbatim
/-- Dense pattern summary group 21 agrees with canonical audited data. -/
theorem densePatternSummaries21_canonical :
    densePatternSummaries21.toList.all patternSummaryCanonicalB = true := by
  decide


-- @@ L26-29 verbatim
/-- Dense hard summary group 0 agrees with canonical audited data. -/
theorem denseHardSummaries00_canonical :
    denseHardSummaries00.toList.all hardSummaryCanonicalB = true := by
  decide


-- @@ L31-34 verbatim
/-- Dense hard summary group 1 agrees with canonical audited data. -/
theorem denseHardSummaries01_canonical :
    denseHardSummaries01.toList.all hardSummaryCanonicalB = true := by
  decide


-- @@ L36-39 verbatim
/-- Dense hard summary group 2 agrees with canonical audited data. -/
theorem denseHardSummaries02_canonical :
    denseHardSummaries02.toList.all hardSummaryCanonicalB = true := by
  decide


-- @@ L41-41 verbatim
end Erdos97Octagon.RawIncidence.StaticDirectCoverage

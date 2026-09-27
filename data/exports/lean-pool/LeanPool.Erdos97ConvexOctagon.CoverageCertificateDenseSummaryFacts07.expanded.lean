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
/-- Dense hard summary group 13 agrees with canonical audited data. -/
theorem denseHardSummaries13_canonical :
    denseHardSummaries13.toList.all hardSummaryCanonicalB = true := by
  decide


-- @@ L21-24 verbatim
/-- Dense hard summary group 14 agrees with canonical audited data. -/
theorem denseHardSummaries14_canonical :
    denseHardSummaries14.toList.all hardSummaryCanonicalB = true := by
  decide


-- @@ L26-29 verbatim
/-- Dense hard summary group 15 agrees with canonical audited data. -/
theorem denseHardSummaries15_canonical :
    denseHardSummaries15.toList.all hardSummaryCanonicalB = true := by
  decide


-- @@ L31-34 verbatim
/-- Dense hard summary group 16 agrees with canonical audited data. -/
theorem denseHardSummaries16_canonical :
    denseHardSummaries16.toList.all hardSummaryCanonicalB = true := by
  decide


-- @@ L36-36 verbatim
end Erdos97Octagon.RawIncidence.StaticDirectCoverage

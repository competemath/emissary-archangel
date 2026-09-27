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
/-- Dense hard summary group 3 agrees with canonical audited data. -/
theorem denseHardSummaries03_canonical :
    denseHardSummaries03.toList.all hardSummaryCanonicalB = true := by
  decide


-- @@ L21-24 verbatim
/-- Dense hard summary group 4 agrees with canonical audited data. -/
theorem denseHardSummaries04_canonical :
    denseHardSummaries04.toList.all hardSummaryCanonicalB = true := by
  decide


-- @@ L26-29 verbatim
/-- Dense hard summary group 5 agrees with canonical audited data. -/
theorem denseHardSummaries05_canonical :
    denseHardSummaries05.toList.all hardSummaryCanonicalB = true := by
  decide


-- @@ L31-34 verbatim
/-- Dense hard summary group 6 agrees with canonical audited data. -/
theorem denseHardSummaries06_canonical :
    denseHardSummaries06.toList.all hardSummaryCanonicalB = true := by
  decide


-- @@ L36-39 verbatim
/-- Dense hard summary group 7 agrees with canonical audited data. -/
theorem denseHardSummaries07_canonical :
    denseHardSummaries07.toList.all hardSummaryCanonicalB = true := by
  decide


-- @@ L41-41 verbatim
end Erdos97Octagon.RawIncidence.StaticDirectCoverage

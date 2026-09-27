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
/-- Dense hard summary group 8 agrees with canonical audited data. -/
theorem denseHardSummaries08_canonical :
    denseHardSummaries08.toList.all hardSummaryCanonicalB = true := by
  decide


-- @@ L21-24 verbatim
/-- Dense hard summary group 9 agrees with canonical audited data. -/
theorem denseHardSummaries09_canonical :
    denseHardSummaries09.toList.all hardSummaryCanonicalB = true := by
  decide


-- @@ L26-29 verbatim
/-- Dense hard summary group 10 agrees with canonical audited data. -/
theorem denseHardSummaries10_canonical :
    denseHardSummaries10.toList.all hardSummaryCanonicalB = true := by
  decide


-- @@ L31-34 verbatim
/-- Dense hard summary group 11 agrees with canonical audited data. -/
theorem denseHardSummaries11_canonical :
    denseHardSummaries11.toList.all hardSummaryCanonicalB = true := by
  decide


-- @@ L36-39 verbatim
/-- Dense hard summary group 12 agrees with canonical audited data. -/
theorem denseHardSummaries12_canonical :
    denseHardSummaries12.toList.all hardSummaryCanonicalB = true := by
  decide


-- @@ L41-41 verbatim
end Erdos97Octagon.RawIncidence.StaticDirectCoverage

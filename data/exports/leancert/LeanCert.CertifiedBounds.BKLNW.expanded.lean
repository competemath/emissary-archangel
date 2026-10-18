/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.CertifiedBounds.BKLNWVerified


-- @@ L8-14 verbatim
/-!
# Certified BKLNW bounds

Stable public interface for the BKLNW `a₂` certificate family. The declarations
here directly expose the checked base lemmas and reflective certificates; example
modules are not part of the public API.
-/


-- @@ L16-16 verbatim
namespace LeanCert.CertifiedBounds.BKLNW


-- @@ L18-18 verbatim
noncomputable abbrev f : ℝ → ℝ := LeanCert.Engine.BKLNW.f

-- @@ L19-19 verbatim
noncomputable abbrev bklnwF : ℝ → Nat → ℝ := LeanCert.Engine.BKLNW.bklnwF


-- @@ L21-21 verbatim
alias floor_log_two_pow := LeanCert.Engine.BKLNW.floor_log_two_pow

-- @@ L22-22 verbatim
alias floor_20 := LeanCert.Engine.BKLNW.floor_20

-- @@ L23-23 verbatim
alias floor_25 := LeanCert.Engine.BKLNW.floor_25

-- @@ L24-24 verbatim
alias floor_30 := LeanCert.Engine.BKLNW.floor_30

-- @@ L25-25 verbatim
alias floor_35 := LeanCert.Engine.BKLNW.floor_35

-- @@ L26-26 verbatim
alias floor_40 := LeanCert.Engine.BKLNW.floor_40

-- @@ L27-27 verbatim
alias floor_43 := LeanCert.Engine.BKLNW.floor_43

-- @@ L28-28 verbatim
alias floor_100 := LeanCert.Engine.BKLNW.floor_100

-- @@ L29-29 verbatim
alias floor_150 := LeanCert.Engine.BKLNW.floor_150

-- @@ L30-30 verbatim
alias floor_200 := LeanCert.Engine.BKLNW.floor_200

-- @@ L31-31 verbatim
alias floor_250 := LeanCert.Engine.BKLNW.floor_250

-- @@ L32-32 verbatim
alias floor_300 := LeanCert.Engine.BKLNW.floor_300

-- @@ L33-33 verbatim
alias f_eq_bklnwF_exp := LeanCert.Engine.BKLNW.f_eq_bklnwF_exp


-- @@ L35-35 verbatim
alias pow29_upper := LeanCert.CertifiedBounds.BKLNW.Verified.pow29_upper

-- @@ L36-36 verbatim
alias pow37_upper := LeanCert.CertifiedBounds.BKLNW.Verified.pow37_upper

-- @@ L37-37 verbatim
alias pow44_upper := LeanCert.CertifiedBounds.BKLNW.Verified.pow44_upper

-- @@ L38-38 verbatim
alias pow51_upper := LeanCert.CertifiedBounds.BKLNW.Verified.pow51_upper

-- @@ L39-39 verbatim
alias pow58_upper := LeanCert.CertifiedBounds.BKLNW.Verified.pow58_upper

-- @@ L40-40 verbatim
alias pow63_upper := LeanCert.CertifiedBounds.BKLNW.Verified.pow63_upper

-- @@ L41-41 verbatim
alias pow145_upper := LeanCert.CertifiedBounds.BKLNW.Verified.pow145_upper

-- @@ L42-42 verbatim
alias pow217_upper := LeanCert.CertifiedBounds.BKLNW.Verified.pow217_upper

-- @@ L43-43 verbatim
alias pow289_upper := LeanCert.CertifiedBounds.BKLNW.Verified.pow289_upper

-- @@ L44-44 verbatim
alias pow361_upper := LeanCert.CertifiedBounds.BKLNW.Verified.pow361_upper

-- @@ L45-45 verbatim
alias pow433_upper := LeanCert.CertifiedBounds.BKLNW.Verified.pow433_upper


-- @@ L47-47 verbatim
alias a2_20_exp_lower := LeanCert.CertifiedBounds.BKLNW.Verified.a2_20_exp_lower

-- @@ L48-48 verbatim
alias a2_20_exp_upper := LeanCert.CertifiedBounds.BKLNW.Verified.a2_20_exp_upper

-- @@ L49-49 verbatim
alias a2_25_exp_lower := LeanCert.CertifiedBounds.BKLNW.Verified.a2_25_exp_lower

-- @@ L50-50 verbatim
alias a2_25_exp_upper := LeanCert.CertifiedBounds.BKLNW.Verified.a2_25_exp_upper

-- @@ L51-51 verbatim
alias a2_30_exp_lower := LeanCert.CertifiedBounds.BKLNW.Verified.a2_30_exp_lower

-- @@ L52-52 verbatim
alias a2_30_exp_upper := LeanCert.CertifiedBounds.BKLNW.Verified.a2_30_exp_upper

-- @@ L53-53 verbatim
alias a2_35_exp_lower := LeanCert.CertifiedBounds.BKLNW.Verified.a2_35_exp_lower

-- @@ L54-54 verbatim
alias a2_35_exp_upper := LeanCert.CertifiedBounds.BKLNW.Verified.a2_35_exp_upper

-- @@ L55-55 verbatim
alias a2_40_exp_lower := LeanCert.CertifiedBounds.BKLNW.Verified.a2_40_exp_lower

-- @@ L56-56 verbatim
alias a2_40_exp_upper := LeanCert.CertifiedBounds.BKLNW.Verified.a2_40_exp_upper

-- @@ L57-57 verbatim
alias a2_43_exp_lower := LeanCert.CertifiedBounds.BKLNW.Verified.a2_43_exp_lower

-- @@ L58-58 verbatim
alias a2_43_exp_upper := LeanCert.CertifiedBounds.BKLNW.Verified.a2_43_exp_upper

-- @@ L59-59 verbatim
alias a2_100_exp_lower := LeanCert.CertifiedBounds.BKLNW.Verified.a2_100_exp_lower

-- @@ L60-60 verbatim
alias a2_100_exp_upper := LeanCert.CertifiedBounds.BKLNW.Verified.a2_100_exp_upper

-- @@ L61-61 verbatim
alias a2_150_exp_lower := LeanCert.CertifiedBounds.BKLNW.Verified.a2_150_exp_lower

-- @@ L62-62 verbatim
alias a2_150_exp_upper := LeanCert.CertifiedBounds.BKLNW.Verified.a2_150_exp_upper

-- @@ L63-63 verbatim
alias a2_200_exp_lower := LeanCert.CertifiedBounds.BKLNW.Verified.a2_200_exp_lower

-- @@ L64-64 verbatim
alias a2_200_exp_upper := LeanCert.CertifiedBounds.BKLNW.Verified.a2_200_exp_upper

-- @@ L65-65 verbatim
alias a2_250_exp_lower := LeanCert.CertifiedBounds.BKLNW.Verified.a2_250_exp_lower

-- @@ L66-66 verbatim
alias a2_250_exp_upper := LeanCert.CertifiedBounds.BKLNW.Verified.a2_250_exp_upper

-- @@ L67-67 verbatim
alias a2_300_exp_lower := LeanCert.CertifiedBounds.BKLNW.Verified.a2_300_exp_lower

-- @@ L68-68 verbatim
alias a2_300_exp_upper := LeanCert.CertifiedBounds.BKLNW.Verified.a2_300_exp_upper


-- @@ L70-70 verbatim
end LeanCert.CertifiedBounds.BKLNW

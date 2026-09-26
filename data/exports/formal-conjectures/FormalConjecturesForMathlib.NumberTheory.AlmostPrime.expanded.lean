/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib.NumberTheory.AlmostPrime



-- @@ L21-21 verbatim
@[expose] public section


-- @@ L23-23 verbatim
namespace Nat


-- @@ L25-25 verbatim
instance (k n : ℕ) : Decidable (IsAlmostPrime k n) := by unfold IsAlmostPrime; infer_instance


-- @@ L27-28 verbatim
instance (k n : ℕ) : Decidable (IsAtMostAlmostPrime k n) := by
  unfold IsAtMostAlmostPrime; infer_instance


-- @@ L30-30 verbatim
end Nat

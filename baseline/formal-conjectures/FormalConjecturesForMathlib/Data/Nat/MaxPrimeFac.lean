/-
Copyright 2025 The Formal Conjectures Authors.

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

public import Mathlib.Data.Nat.MaxPrimeFac

@[expose] public section

namespace Nat

/-- The upstream implementation agrees with the previously pinned definition, including 0 and 1. -/
lemma maxPrimeFac_eq_legacy (n : ℕ) :
    maxPrimeFac n = if n = 1 then 1 else n.primeFactorsList.getLastI := by
  by_cases h : n = 1
  · subst n
    simp
  · obtain rfl | hn : n = 0 ∨ 1 < n := by omega
    · simp [maxPrimeFac, List.getLastI]
    · have hlist := (primeFactorsList_ne_nil n).2 hn
      cases hs : n.primeFactorsList with
      | nil => exact (hlist hs).elim
      | cons a as =>
        simp [maxPrimeFac, h, hs, List.getLastI_eq_getLast?_getD,
          List.getLastD_eq_getLast?, List.getLast?_eq_getLast_of_ne_nil (List.cons_ne_nil a as)]

end Nat

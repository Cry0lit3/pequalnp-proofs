import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

-- With a single nested AND pair, an operand of the upper AND reaches the lower one through ORs.
theorem PEqualNP.Outside.R_meta_1961_1 :
  (let R := fun (n : ℕ) (C : Circuit) (i j : ℕ) =>
      (gateAt C i).op = GateOp.and ∧ (gateAt C j).op = GateOp.and ∧ InCone n C i j
    ∀ (n : ℕ) (C : Circuit), Monotone2 C → andPairs n C ≤ 1 →
      ∀ b t, R n C b t → (∀ i j, R n C i j → i = b ∧ j = t) ∧ (∃ w ∈ (gateAt C t).inputs, OrReaches n C w b)) →
  (let R := fun (n : ℕ) (C : Circuit) (i j : ℕ) =>
      (gateAt C i).op = GateOp.and ∧ (gateAt C j).op = GateOp.and ∧ InCone n C i j
    let offsets := ({0, 1, 3, 9} : Finset (Fin 13))
    let ok := fun (C : Circuit) =>
      (∀ p l : Fin 13, p - l ∈ offsets →
        C.eval (List.ofFn (fun q : Fin 13 => decide (q = p)) ++
          List.ofFn (fun m : Fin 13 => decide (m = l))) = true) ∧
      ∀ P : Finset (Fin 13), P.card = 4 → (∀ l, (P.filter (fun p => p - l ∈ offsets)).card ≤ 2) →
        C.eval (List.ofFn (fun p : Fin 13 => decide (p ∈ P)) ++
          List.ofFn (fun l : Fin 13 => decide (∀ p ∈ P, p - l ∉ offsets))) = false
    ∀ (C : Circuit) (b t : ℕ), Monotone2 C → ReadsBack 26 C → ok C → C.size < 64 →
      (∀ g ∈ C.gates, g.inputs.length = 2 ∧ g.inputs.getD 0 0 ≠ g.inputs.getD 1 0) →
      R 26 C b t → (∀ i j, R 26 C i j → i = b ∧ j = t) →
      (∃ w ∈ (gateAt C t).inputs, OrReaches 26 C w b) →
      ∃ D : Circuit, Monotone2 D ∧ ReadsBack 26 D ∧ ok D ∧ D.size < C.size) →
  have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x3 x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card = (4 : ℕ) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x3 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x7 - x6 ∉ x1)) = Bool.false; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => ∃ (x4 : ℕ) (x5 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x3 x4 x5; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x4 → x2 x4 → x4.size < (64 : ℕ) → x3 x4 → (∀ x10 ∈ x4.gates, x10.inputs.length = (2 : ℕ) ∧ x10.inputs.getD (0 : ℕ) (0 : ℕ) ≠ x10.inputs.getD (1 : ℕ) (0 : ℕ)) → PEqualNP.TopForm.andPairs (26 : ℕ) x4 ≤ (1 : ℕ) → ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x12 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x12 ∧ x2 x12 ∧ x12.size < x4.size := by
  intro isolate shorten
  dsimp only
  intro C mono back good small nested arity count
  obtain ⟨b, t, bottom, top, cone⟩ := nested
  obtain ⟨unique, route⟩ := isolate 26 C mono count b t ⟨bottom, top, cone⟩
  exact shorten C b t mono back good small arity ⟨bottom, top, cone⟩ unique route

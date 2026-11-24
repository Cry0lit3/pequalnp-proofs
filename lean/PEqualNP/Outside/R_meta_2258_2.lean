import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity.NestedCover

-- A vertex cover after deleting U misses only edges in U.
-- Enumerating the vertex subsets of Fin 11 gives the lower-bound table.
-- The gate-count inequality then handles zero or one missed edge directly.
theorem PEqualNP.Outside.R_meta_2258_2 :
  (let floor : ℕ → ℕ := fun m => [7, 6, 5, 4, 4, 3, 3, 3, 2, 2, 2, 2, 1, 1, 1, 1].getD m 0
    ∀ (U : Finset (Sym2 (Fin 11))) (K : Finset (Fin 11)),
      ((edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
        (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]).deleteEdges ↑U).IsVertexCover (↑K : Set (Fin 11)) →
      floor U.card ≤ K.card) →
  (let floor : ℕ → ℕ := fun m => [7, 6, 5, 4, 4, 3, 3, 3, 2, 2, 2, 2, 1, 1, 1, 1].getD m 0
    ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (D : Circuit),
      G = edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
        (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)] → IsLeastAO G D → TopForm G D →
      let U := Ustar G D
      let T := tops G D
      let J := junk G D
      (∀ a ∈ T, let S : Fin 2 → Finset (Fin 11) := side D a
        (∀ u ∈ S 0, ∀ v ∈ S 1, G.Adj u v) ∧ ((S 0).card ≤ 1 ∨ (S 1).card ≤ 1)) →
      (∀ u v : Fin 11, s(u, v) ∈ U → ∃ a ∈ T, ∃ b : Fin 2, ∃ j ∈ J,
        gateVal 11 D a (pairInput u v) = true ∧ OrReaches 11 D (opnd D a b) j ∧
        gateVal 11 D j (pairInput u v) = true) →
      2 ≤ U.card → 3 ≤ J.card → D.size ≤ 21 →
      U.card + 7 ≤ floor U.card + 2 * (centreless G D).card + J.card + (orN G D \ lam G D).card) →
  ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         have x7 : Finset ℕ := PEqualNP.TopForm.tops x1 x3;         have x8 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;         have x9 : Finset ℕ := PEqualNP.TopForm.junk x1 x3;         have x10 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;         (∀ x11 ∈ x7,             have x13 : Fin (2 : ℕ) → Finset (Fin (11 : ℕ)) := PEqualNP.TopForm.side x3 x11;             (∀ x14 ∈ x13 (0 : Fin (2 : ℕ)), ∀ x16 ∈ x13 (1 : Fin (2 : ℕ)), x1.Adj x14 x16) ∧ ((x13 (0 : Fin (2 : ℕ))).card ≤ (1 : ℕ) ∨ (x13 (1 : Fin (2 : ℕ))).card ≤ (1 : ℕ))) →           (∀ (x12 x13 : Fin (11 : ℕ)), s(x12, x13) ∈ x10 → ∃ x15 ∈ x7, ∃ (x16 : Fin (2 : ℕ)), ∃ x17 ∈ x9, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x15 (PEqualNP.EdgeOwnership.pairInput x12 x13) = Bool.true ∧ PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x3 (PEqualNP.TopForm.opnd x3 x15 x16) x17 ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x17 (PEqualNP.EdgeOwnership.pairInput x12 x13) = Bool.true) → (15 : ℕ) + (x7 \ x8).card + (2 : ℕ) * x8.card + x9.card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card ≤ x3.size + x10.card → (∀ (x14 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x10) x14 → x14.card ≤ (x7 \ x8).card) → (3 : ℕ) ≤ x9.card → (22 : ℕ) ≤ x3.size := by
  intro profile charge G _ D hG least top
  dsimp only
  intro stars trace count coverBound threeJunk
  let floor : ℕ → ℕ := fun m => [7, 6, 5, 4, 4, 3, 3, 3, 2, 2, 2, 2, 1, 1, 1, 1].getD m 0
  let U := Ustar G D
  let T := tops G D
  let Z := centreless G D
  let J := junk G D
  let R := orN G D \ lam G D
  change 15 + (T \ Z).card + 2 * Z.card + J.card + R.card ≤ D.size + U.card at count
  change 3 ≤ J.card at threeJunk
  classical
  let H := G.deleteEdges (↑U : Set (Sym2 (Fin 11)))
  let covers : Finset (Finset (Fin 11)) :=
    Finset.univ.filter (fun K => H.IsVertexCover (↑K : Set (Fin 11)))
  have nonempty : covers.Nonempty := by
    refine ⟨Finset.univ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    intro u v _
    exact Or.inl (Finset.mem_univ u)
  obtain ⟨K, memberK, leastK⟩ := Finset.exists_min_image covers Finset.card nonempty
  have cover : H.IsVertexCover (↑K : Set (Fin 11)) := (Finset.mem_filter.mp memberK).2
  have minK : IsMinCover H K := ⟨cover, fun K' hc =>
    leastK K' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)⟩
  have counted : K.card ≤ (T \ Z).card := coverBound K minK
  have onGraph : (G.deleteEdges (↑U : Set (Sym2 (Fin 11)))).IsVertexCover (↑K : Set (Fin 11)) := cover
  rw [hG] at onGraph
  have finiteBound : floor U.card ≤ K.card := profile U K onGraph
  by_contra tooSmall
  have short : D.size ≤ 21 := by omega
  by_cases many : 2 ≤ U.card
  · have paid : U.card + 7 ≤ floor U.card + 2 * Z.card + J.card + R.card :=
      charge G D hG least top stars trace many threeJunk short
    omega
  · have one : U.card = 0 ∨ U.card = 1 := by omega
    rcases one with zero | single
    · rw [zero] at finiteBound
      change 7 ≤ K.card at finiteBound
      omega
    · rw [single] at finiteBound
      change 6 ≤ K.card at finiteBound
      omega

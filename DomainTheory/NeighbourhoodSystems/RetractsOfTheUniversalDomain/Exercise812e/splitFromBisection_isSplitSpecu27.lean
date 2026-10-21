/-ai
The bisection split satisfies the split specification whenever every neighbourhood of the target presentation is nonempty.

If the input is presented, unfold the split at that triple. An empty intersection makes the difference the whole prober set, and the empty-union and empty-intersection identities give the specification; an empty difference is symmetric. If neither decider fires, both halves are nonempty target neighbourhoods, and the bisection supplies the union and the disjointness. If the input is not presented, the definition is the choice split, which satisfies the specification.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e.Basic

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.UnionClosed
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive


namespace ComputableBisection

variable {α γ : Type*} {V : NeighborhoodSystem α} {W : NeighborhoodSystem γ}
  (P : ComputablePresentation V) (hDiff : IsComputableDiff P)
  {Q : ComputablePresentation W} (B : ComputableBisection Q) (hWnomin : W.NoMinimal)











/-- **`splitFromBisection` satisfies `SplitSpec'`**, completing the concrete-construction half of
`8.12(g)(3)`. Needs one extra hypothesis beyond `isComputableSplit_ofBisection`'s own,
`hQne : ∀ j, Q.X j ≠ ∅` — true for both `U`/`V` (every `ComputablePresentation` index is `mem`-
genuine, and both systems' `mem` structurally excludes `∅`; see `Exercise812.lean` line 199/
`Definition87.lean` line 96) but not derivable from `ComputableBisection`'s abstract fields alone
(nothing there stops `Q.X (B.left m)`, say, from being `∅` in general — only used in the "neither
decider fires" branch, to show the bisection's two halves are each individually `≠ ∅`, matching that
branch's `A ∩ Xn ≠ ∅ ↔ .1 ≠ ∅`/`A \ Xn ≠ ∅ ↔ .2 ≠ ∅` obligations). The two decider-fires branches
need no such hypothesis at all — `.1`/`.2` there are literally `∅`/`B'`, and the requisite `↔`s
reduce to `hAB` via the algebraic facts `A ∩ Xn = ∅ → A \ Xn = A` (resp. `A \ Xn = ∅ → A ∩ Xn = A`).
The "not presented" branch reduces to exactly `splitChoice'_isSplitSpec` (`Exercise812c.lean`),
verbatim. -/
theorem splitFromBisection_isSplitSpec' (hpos : V.IsPositive) (hnomin : V.NoMinimal)
    (hdiffClosed : V.DiffClosed) (hQne : ∀ j, Q.X j ≠ ∅) :
    SplitSpec' W (splitFromBisection P hDiff B hWnomin) := by
  intro A B' hAB hBW Xn
  by_cases h : ∃ n m k, A = P.X n ∧ B' = Q.X m ∧ Xn = P.X k
  · obtain ⟨n, m, k, rfl, rfl, rfl⟩ := h
    rw [splitFromBisection_eq P hDiff B hWnomin hpos hnomin hdiffClosed n m k]
    by_cases h1 : emptyInterDec P (Nat.pair n k) = 1
    · have hInterEmpty : P.X n ∩ P.X k = ∅ := (emptyInterDec_eq_one_iff P hpos hnomin n k).mp h1
      have hdiffEq : P.X n \ P.X k = P.X n := by
        ext x
        simp only [Set.mem_sdiff]
        exact ⟨fun hx => hx.1, fun hx =>
          ⟨hx, fun hxk => Set.eq_empty_iff_forall_notMem.mp hInterEmpty x ⟨hx, hxk⟩⟩⟩
      rw [ite_eq_left h1]
      refine ⟨Or.inl rfl, hBW, iff_of_true hInterEmpty rfl, ?_, Set.empty_union _,
        Set.empty_inter _⟩
      rw [hdiffEq]; exact hAB
    · by_cases h2 : emptyDiffDec P hDiff (Nat.pair n k) = 1
      · have hDiffEmpty : P.X n \ P.X k = ∅ :=
          (emptyDiffDec_eq_one_iff P hDiff hdiffClosed hnomin n k).mp h2
        have hInterEq : P.X n ∩ P.X k = P.X n := by
          ext x
          simp only [Set.mem_inter_iff]
          refine ⟨fun hx => hx.1, fun hx => ⟨hx, ?_⟩⟩
          by_contra hxk
          exact Set.eq_empty_iff_forall_notMem.mp hDiffEmpty x ⟨hx, hxk⟩
        rw [ite_eq_right h1, ite_eq_left h2]
        refine ⟨hBW, Or.inl rfl, ?_, iff_of_true hDiffEmpty rfl, Set.union_empty _,
          Set.inter_empty _⟩
        rw [hInterEq]; exact hAB
      · have h1' : P.X n ∩ P.X k ≠ ∅ :=
          fun he => h1 ((emptyInterDec_eq_one_iff P hpos hnomin n k).mpr he)
        have h2' : P.X n \ P.X k ≠ ∅ :=
          fun he => h2 ((emptyDiffDec_eq_one_iff P hDiff hdiffClosed hnomin n k).mpr he)
        rw [ite_eq_right h1, ite_eq_right h2]
        exact ⟨Or.inr (Q.mem_X _), Or.inr (Q.mem_X _), iff_of_false h1' (hQne _),
          iff_of_false h2' (hQne _), B.union m, B.disjoint m⟩
  · unfold splitFromBisection
    rw [dite_eq_right h]
    exact splitChoice'_isSplitSpec W hWnomin hAB hBW Xn

end ComputableBisection
end DomainTheory.NeighbourhoodSystems

module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise_1_26

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
namespace NeighborhoodSystem
section

variable {α : Type*} (V : NeighborhoodSystem α)

/- concordance: source L546 EXERCISE 1.27 suprema of bounded sets -/
/-- **Exercise 1.27 — bounded set of elements.** `X ⊆ |𝒟|` is *bounded* iff it has an upper
bound `y ∈ |𝒟|`: `x ⊑ y` for all `x ∈ X`. -/
def Bounded (X : Set V.Element) : Prop := ∃ y : V.Element, ∀ x ∈ X, x ≤ y

/-- The two-term sequence `⟨U, W⟩` as a function `ℕ → Set α` (used to phrase `Consistent`). -/
def pairSeq (U W : Set α) : ℕ → Set α := fun i => if i = 0 then U else W

/-- The family of upper bounds of `X`: `{y ∣ x ⊑ y for all x ∈ X}`. -/
def upperBounds (X : Set V.Element) : Set V.Element := {y | ∀ x ∈ X, x ≤ y}

/-- If `X` is bounded then its upper-bound family is non-empty (it contains the witness). -/
theorem upperBounds_nonempty {X : Set V.Element} (hX : V.Bounded X) :
    (V.upperBounds X).Nonempty :=
  hX.imp fun _ hy => hy

/-- **Exercise 1.27 — `⊔X`.** The least upper bound of a bounded `X`, defined à la Scott as the
intersection of all upper bounds: `⊔X = ⋂ {y ∣ x ⊑ y all x∈X}`. Reusing `sInf` from Exercise
1.18 on the (non-empty, because bounded) family of upper bounds. -/
def sSup (X : Set V.Element) (hX : V.Bounded X) : V.Element :=
  V.sInf (V.upperBounds X) (V.upperBounds_nonempty hX)

/-- **Exercise 1.27 — boundedness is finitary.** `X ⊆ |𝒟|` is bounded iff every *finite* subset
of `X` is bounded. The forward direction reuses any global bound. The reverse direction is the
content: assemble `C = ⋃_{x∈X} x` (the neighbourhoods of all members of `X`); `C` is finitely
consistent because any finite sequence drawn from `C` comes from finitely many members of `X`,
which form a finite subset, hence bounded — that bound's filter contains the whole finite
sequence, so its intersection lies in `𝒟`. The least filter `leastFilter C` (Exercise 1.18) is
then an upper bound of `X`. -/
theorem bounded_iff_finite_bounded (X : Set V.Element) :
    V.Bounded X ↔ ∀ S : Set V.Element, S ⊆ X → S.Finite → V.Bounded S := by
  constructor
  · rintro ⟨y, hy⟩ S hS _
    exact ⟨y, fun x hx => hy x (hS hx)⟩
  · intro hfin
    set C : Set (Set α) := {Z | ∃ x : V.Element, x ∈ X ∧ x.mem Z} with hCdef
    have hCsub : ∀ Z ∈ C, V.mem Z := by rintro Z ⟨x, _, hxZ⟩; exact x.sub hxZ
    have hCcons : V.FinitelyConsistent C := by
      intro n seq hseqC
      choose g hgX hgmem using hseqC
      set S : Set V.Element := Set.range (fun i : Fin n => g i.1 i.2) with hSdef
      have hSfin : S.Finite := Set.finite_range _
      have hSsub : S ⊆ X := by
        rintro _ ⟨i, rfl⟩
        exact hgX i.1 i.2
      obtain ⟨y, hy⟩ := hfin S hSsub hSfin
      have hseqy : ∀ i, i < n → y.mem (seq i) := by
        intro i hi
        have hle : g i hi ≤ y := hy _ ⟨⟨i, hi⟩, rfl⟩
        exact hle (seq i) (hgmem i hi)
      have hmem : y.mem (V.interUpTo seq n) := y.mem_interUpTo seq hseqy
      exact ⟨V.interUpTo seq n, y.sub hmem, subset_rfl⟩
    refine ⟨V.leastFilter C hCsub hCcons, ?_⟩
    intro x hx Z hZ
    exact V.subset_leastFilter C hCsub hCcons ⟨x, hx, hZ⟩

theorem interUpTo_pairSeq (U W : Set α) :
    V.interUpTo (pairSeq U W) 2 = V.master ∩ U ∩ W := by
  simp only [interUpTo_succ, interUpTo_zero, pairSeq]
  norm_num

/-- **Exercise 1.27 — "boundedness is for elements what consistency is for neighbourhoods".**
For `U, W ∈ 𝒟`, the pair `⟨U, W⟩` is consistent in `𝒟` iff `{↑U, ↑W}` is bounded in `|𝒟|`.

`→` packages the consistency witness `Z` into the principal filter `↑Z`, which lies above both
`↑U` and `↑W` (via `principal_le_iff`). `←` uses that any bound `y` contains both `U` and `W`,
hence `U ∩ W ∈ y ⊆ 𝒟`, giving `U ∩ W` as the consistency witness. -/
theorem consistent_pair_iff_bounded {U W : Set α} (hU : V.mem U) (hW : V.mem W) :
    V.Consistent (pairSeq U W) 2 ↔ V.Bounded {V.principal hU, V.principal hW} := by
  constructor
  · rintro ⟨Z, hZmem, hZsub⟩
    rw [V.interUpTo_pairSeq] at hZsub
    have hZU : Z ⊆ U := hZsub.trans (Set.inter_subset_left.trans Set.inter_subset_right)
    have hZW : Z ⊆ W := hZsub.trans Set.inter_subset_right
    refine ⟨V.principal hZmem, ?_⟩
    intro x hx
    rcases hx with rfl | rfl
    · exact (V.principal_le_iff hU hZmem).mpr hZU
    · exact (V.principal_le_iff hW hZmem).mpr hZW
  · rintro ⟨y, hy⟩
    have hyU : y.mem U :=
      hy _ (Or.inl rfl) U ⟨hU, subset_rfl⟩
    have hyW : y.mem W :=
      hy _ (Or.inr rfl) W ⟨hW, subset_rfl⟩
    have hyUW : y.mem (U ∩ W) := y.inter_mem hyU hyW
    refine ⟨U ∩ W, y.sub hyUW, ?_⟩
    rw [V.interUpTo_pairSeq]
    intro z hz
    exact ⟨⟨V.sub_master hU hz.1, hz.1⟩, hz.2⟩

/-- **Exercise 1.27 — `⊔X` is an upper bound.** Each `x ∈ X` satisfies `x ⊑ ⊔X`. -/
theorem le_sSup (X : Set V.Element) (hX : V.Bounded X) {x : V.Element} (hx : x ∈ X) :
    x ≤ V.sSup X hX :=
  V.le_sInf (V.upperBounds X) (V.upperBounds_nonempty hX) x (fun _ hy => hy x hx)

/-- **Exercise 1.27 — `⊔X` is least.** Any upper bound `z` of `X` satisfies `⊔X ⊑ z`. -/
theorem sSup_le (X : Set V.Element) (hX : V.Bounded X) {z : V.Element}
    (hz : ∀ x ∈ X, x ≤ z) : V.sSup X hX ≤ z :=
  V.sInf_le (V.upperBounds X) (V.upperBounds_nonempty hX) hz
end

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.NeighborhoodSystem
section

set_option linter.unusedVariables false

theorem example_127.{u_1} : And
  (And
    (And
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
        (X : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)),
        Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α V X)
          (∀ (S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)),
            @LE.le (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@Set.instLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) S X →
              @Set.Finite (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) S →
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α V S))
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) {U W : Set α}
        (hU : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V U)
        (hW : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V W),
        Iff
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Consistent α V
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.pairSeq α U W)
            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α V
            (@Insert.insert (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
              (@Set.instInsert (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal α V U hU)
              (@Singleton.singleton (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@Set.instSingletonSet (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal α V W hW))))))
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
      (X : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
      (hX : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α V X)
      {x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V},
      @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
          (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) X x →
        @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
          x (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup α V X hX)))
  (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
    (X : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
    (hX : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α V X)
    {z : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V},
    (∀ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
        @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
            (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) X x →
          @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
            x z) →
      @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup α V X hX) z) :=
  @And.intro
  (And
    (And
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
        (X : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)),
        Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α V X)
          (∀ (S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)),
            @LE.le (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@Set.instLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) S X →
              @Set.Finite (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) S →
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α V S))
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) {U W : Set α}
        (hU : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V U)
        (hW : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V W),
        Iff
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Consistent α V
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.pairSeq α U W)
            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α V
            (@Insert.insert (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
              (@Set.instInsert (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal α V U hU)
              (@Singleton.singleton (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@Set.instSingletonSet (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal α V W hW))))))
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
      (X : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
      (hX : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α V X)
      {x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V},
      @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
          (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) X x →
        @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
          x (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup α V X hX)))
  (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
    (X : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
    (hX : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α V X)
    {z : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V},
    (∀ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
        @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
            (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) X x →
          @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
            x z) →
      @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup α V X hX) z)
  (@And.intro
    (And
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
        (X : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)),
        Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α V X)
          (∀ (S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)),
            @LE.le (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@Set.instLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) S X →
              @Set.Finite (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) S →
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α V S))
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) {U W : Set α}
        (hU : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V U)
        (hW : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V W),
        Iff
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Consistent α V
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.pairSeq α U W)
            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α V
            (@Insert.insert (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
              (@Set.instInsert (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal α V U hU)
              (@Singleton.singleton (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@Set.instSingletonSet (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal α V W hW))))))
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
      (X : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
      (hX : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α V X)
      {x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V},
      @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
          (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) X x →
        @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
          x (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup α V X hX))
    (@And.intro
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
        (X : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)),
        Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α V X)
          (∀ (S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)),
            @LE.le (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@Set.instLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) S X →
              @Set.Finite (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) S →
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α V S))
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) {U W : Set α}
        (hU : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V U)
        (hW : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V W),
        Iff
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Consistent α V
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.pairSeq α U W)
            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α V
            (@Insert.insert (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
              (@Set.instInsert (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal α V U hU)
              (@Singleton.singleton (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@Set.instSingletonSet (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal α V W hW)))))
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bounded_iff_finite_bounded
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.consistent_pair_iff_bounded)
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.le_sSup)
  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup_le
end

end DomainTheory.NeighbourhoodSystems.NeighborhoodSystem
namespace DomainTheory.NeighbourhoodSystems
namespace NeighborhoodSystem
section

variable {α : Type*} (V : NeighborhoodSystem α)

/-- Scott's `[X] = {x ∈ |𝒟| ∣ X ∈ x}`: the elements of `|𝒟|` that contain the neighbourhood `X`.
(This is the `basicOpen X` of Exercise 1.22, repeated here to avoid the topology dependency.) -/
def bracket (X : Set α) : Set V.Element := {x | x.mem X}

@[simp] theorem mem_bracket {X : Set α} {x : V.Element} : x ∈ V.bracket X ↔ x.mem X := Iff.rfl

@[simp] theorem bracket_master : V.bracket V.master = Set.univ := by
  ext x; simp only [mem_bracket, Set.mem_univ, iff_true]; exact x.master_mem

/-- **Theorem 1.10 (3).** `[X] ∩ [Y] = [X ∩ Y]` for `X, Y ∈ 𝒟`. (`⊆` is filter closure under `∩`;
`⊇` is upward closure along `X ∩ Y ⊆ X`, `X ∩ Y ⊆ Y`.) -/
theorem bracket_inter {X Y : Set α} (hX : V.mem X) (hY : V.mem Y) :
    V.bracket X ∩ V.bracket Y = V.bracket (X ∩ Y) := by
  ext x
  simp only [Set.mem_inter_iff, mem_bracket]
  constructor
  · rintro ⟨hx, hy⟩
    exact x.inter_mem hx hy
  · intro hxy
    exact ⟨x.up_mem hxy hX Set.inter_subset_left, x.up_mem hxy hY Set.inter_subset_right⟩

/-- **Theorem 1.10 (4).** `↑X ∈ [X]`: the principal filter of `X` contains `X`. -/
theorem principal_mem_bracket {X : Set α} (hX : V.mem X) : V.principal hX ∈ V.bracket X :=
  ⟨hX, subset_rfl⟩

/-- **The correspondence `X ↦ [X]` is inclusion-preserving.** `[X] ⊆ [Y] ↔ X ⊆ Y` (for `X,Y ∈ 𝒟`).
`→` tests at `↑X ∈ [X]`, reading `X ⊆ Y` off `↑X ∈ [Y]`; `←` is upward closure. -/
theorem bracket_subset_iff {X Y : Set α} (hX : V.mem X) (hY : V.mem Y) :
    V.bracket X ⊆ V.bracket Y ↔ X ⊆ Y := by
  constructor
  · intro h
    exact (h (V.principal_mem_bracket hX)).2
  · intro hXY x hx
    exact x.up_mem hx hY hXY

/-- **The correspondence `X ↦ [X]` is one-one.** `[X] = [Y] ⟹ X = Y` (for `X,Y ∈ 𝒟`). -/
theorem bracket_injective {X Y : Set α} (hX : V.mem X) (hY : V.mem Y)
    (h : V.bracket X = V.bracket Y) : X = Y :=
  Set.Subset.antisymm ((V.bracket_subset_iff hX hY).mp h.subset)
    ((V.bracket_subset_iff hY hX).mp h.superset)
end

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end

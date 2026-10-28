module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise_1_18
import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Factoid_1_7
import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Factoid_1_5
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.principal
public import Mathlib.Basic.Finite.Defs

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
namespace NeighborhoodSystem
section

variable {α : Type*} (V : NeighborhoodSystem α)

def Bounded (X : Set V.Element) : Prop := ∃ y : V.Element, ∀ x ∈ X, x ≤ y

def pairSeq (U W : Set α) : ℕ → Set α := fun i => if i = 0 then U else W

def upperBounds (X : Set V.Element) : Set V.Element := {y | ∀ x ∈ X, x ≤ y}

theorem upperBounds_nonempty {X : Set V.Element} (hX : V.Bounded X) :
    (V.upperBounds X).Nonempty :=
  hX.imp fun _ hy => hy

def sSup (X : Set V.Element) (hX : V.Bounded X) : V.Element :=
  V.sInf (V.upperBounds X) (V.upperBounds_nonempty hX)

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

theorem le_sSup (X : Set V.Element) (hX : V.Bounded X) {x : V.Element} (hx : x ∈ X) :
    x ≤ V.sSup X hX :=
  V.le_sInf (V.upperBounds X) (V.upperBounds_nonempty hX) x (fun _ hy => hy x hx)

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

def bracket (X : Set α) : Set V.Element := {x | x.mem X}

@[simp] theorem mem_bracket {X : Set α} {x : V.Element} : x ∈ V.bracket X ↔ x.mem X := Iff.rfl

@[simp] theorem bracket_master : V.bracket V.master = Set.univ := by
  ext x; simp only [mem_bracket, Set.mem_univ, iff_true]; exact x.master_mem

theorem bracket_inter {X Y : Set α} (hX : V.mem X) (hY : V.mem Y) :
    V.bracket X ∩ V.bracket Y = V.bracket (X ∩ Y) := by
  ext x
  simp only [Set.mem_inter_iff, mem_bracket]
  constructor
  · rintro ⟨hx, hy⟩
    exact x.inter_mem hx hy
  · intro hxy
    exact ⟨x.up_mem hxy hX Set.inter_subset_left, x.up_mem hxy hY Set.inter_subset_right⟩

theorem principal_mem_bracket {X : Set α} (hX : V.mem X) : V.principal hX ∈ V.bracket X :=
  ⟨hX, subset_rfl⟩

theorem bracket_subset_iff {X Y : Set α} (hX : V.mem X) (hY : V.mem Y) :
    V.bracket X ⊆ V.bracket Y ↔ X ⊆ Y := by
  constructor
  · intro h
    exact (h (V.principal_mem_bracket hX)).2
  · intro hXY x hx
    exact x.up_mem hx hY hXY

theorem bracket_injective {X Y : Set α} (hX : V.mem X) (hY : V.mem Y)
    (h : V.bracket X = V.bracket Y) : X = Y :=
  Set.Subset.antisymm ((V.bracket_subset_iff hX hY).mp h.subset)
    ((V.bracket_subset_iff hY hX).mp h.superset)
end

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end

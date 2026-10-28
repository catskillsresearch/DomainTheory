module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise_1_24

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise_1_18

@[expose] public section

section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*} {V : NeighborhoodSystem α}

namespace NeighborhoodSystem

def preFix (f : V.Element → V.Element) : Set V.Element := {x | f x ≤ x}

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace NeighborhoodSystem

@[simp] theorem mem_preFix {f : V.Element → V.Element} {x : V.Element} :
    x ∈ preFix f ↔ f x ≤ x := Iff.rfl

def monoFix (f : V.Element → V.Element) {a : V.Element} (ha : f a ≤ a) : V.Element :=
  V.sInf (preFix f) ⟨a, ha⟩

theorem exists_unique_nat_rec {Z : Type*} (z : Z) (op : Z → Z) :
    ∃! s : ℕ → Z, s 0 = z ∧ ∀ n, s (n + 1) = op (s n) := by
  refine ⟨fun n => Nat.rec z (fun _ x => op x) n, ⟨rfl, fun _ => rfl⟩, ?_⟩
  rintro s ⟨h0, hsucc⟩
  funext n
  induction n with
  | zero => exact h0
  | succ k ih => rw [hsucc k, ih]

theorem monoFix_le_preFix (f : V.Element → V.Element) {a : V.Element} (ha : f a ≤ a)
    {x : V.Element} (hx : f x ≤ x) : monoFix f ha ≤ x :=
  V.sInf_le (preFix f) ⟨a, ha⟩ hx

theorem monoFix_le (f : V.Element → V.Element) {a : V.Element} (ha : f a ≤ a) :
    monoFix f ha ≤ a := monoFix_le_preFix f ha ha

theorem monoFix_least (f : V.Element → V.Element) {a : V.Element} (ha : f a ≤ a)
    {y : V.Element} (hy : f y = y) : monoFix f ha ≤ y :=
  monoFix_le_preFix f ha (le_of_eq hy)

theorem monoFix_preFix (f : V.Element → V.Element) (hf : Monotone f) {a : V.Element}
    (ha : f a ≤ a) : f (monoFix f ha) ≤ monoFix f ha := by
  apply V.le_sInf (preFix f) ⟨a, ha⟩
  intro x hx
  exact le_trans (hf (monoFix_le_preFix f ha hx)) hx

theorem monoFix_isFixed (f : V.Element → V.Element) (hf : Monotone f) {a : V.Element}
    (ha : f a ≤ a) : f (monoFix f ha) = monoFix f ha := by
  have hfb : f (monoFix f ha) ≤ monoFix f ha := monoFix_preFix f hf ha
  have hbf : monoFix f ha ≤ f (monoFix f ha) :=
    monoFix_le_preFix f ha (hf hfb)
  exact le_antisymm hfb hbf

theorem nat_iterate_unique {s : ℕ → ℕ} (h0 : s 0 = 0) (hsucc : ∀ n, s (n + 1) = s n + 1) :
    ∀ n, s n = n := by
  intro n
  induction n with
  | zero => exact h0
  | succ k ih => rw [hsucc k, ih]

end NeighborhoodSystem
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.NeighborhoodSystem
section
set_option linter.unusedVariables false

theorem example_413.{u_1, u_2} : And
  (And
    (And
      (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        (f :
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V →
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
        @Monotone (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
            f →
          ∀ {a : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V}
            (ha :
              @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
                (f a) a),
            @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (f (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.monoFix α V f a ha))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.monoFix α V f a ha))
      (∀ {Z : Type u_2} (z : Z) (op : Z → Z),
        @ExistsUnique (Nat → Z) fun (s : Nat → Z) =>
          And (@Eq Z (s (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) z)
            (∀ (n : Nat),
              @Eq Z
                (s
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (op (s n)))))
    (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (f :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
      {a : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V}
      (ha :
        @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
          (f a) a)
      {y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V},
      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (f y) y →
        @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.monoFix α V f a ha) y))
  (∀ {s : Nat → Nat},
    @Eq Nat (s (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
      (∀ (n : Nat),
          @Eq Nat
            (s
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (s n)
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
        ∀ (n : Nat), @Eq Nat (s n) n) :=
  @And.intro
  (And
    (And
      (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        (f :
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V →
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
        @Monotone (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
            f →
          ∀ {a : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V}
            (ha :
              @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
                (f a) a),
            @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (f (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.monoFix α V f a ha))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.monoFix α V f a ha))
      (∀ {Z : Type u_2} (z : Z) (op : Z → Z),
        @ExistsUnique (Nat → Z) fun (s : Nat → Z) =>
          And (@Eq Z (s (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) z)
            (∀ (n : Nat),
              @Eq Z
                (s
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (op (s n)))))
    (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (f :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
      {a : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V}
      (ha :
        @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
          (f a) a)
      {y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V},
      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (f y) y →
        @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.monoFix α V f a ha) y))
  (∀ {s : Nat → Nat},
    @Eq Nat (s (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
      (∀ (n : Nat),
          @Eq Nat
            (s
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (s n)
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
        ∀ (n : Nat), @Eq Nat (s n) n)
  (@And.intro
    (And
      (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        (f :
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V →
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
        @Monotone (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
            f →
          ∀ {a : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V}
            (ha :
              @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
                (f a) a),
            @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (f (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.monoFix α V f a ha))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.monoFix α V f a ha))
      (∀ {Z : Type u_2} (z : Z) (op : Z → Z),
        @ExistsUnique (Nat → Z) fun (s : Nat → Z) =>
          And (@Eq Z (s (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) z)
            (∀ (n : Nat),
              @Eq Z
                (s
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (op (s n)))))
    (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (f :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
      {a : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V}
      (ha :
        @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
          (f a) a)
      {y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V},
      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (f y) y →
        @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.monoFix α V f a ha) y)
    (@And.intro
      (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        (f :
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V →
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
        @Monotone (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
            f →
          ∀ {a : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V}
            (ha :
              @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
                (f a) a),
            @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (f (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.monoFix α V f a ha))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.monoFix α V f a ha))
      (∀ {Z : Type u_2} (z : Z) (op : Z → Z),
        @ExistsUnique (Nat → Z) fun (s : Nat → Z) =>
          And (@Eq Z (s (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) z)
            (∀ (n : Nat),
              @Eq Z
                (s
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (op (s n))))
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.monoFix_isFixed
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.exists_unique_nat_rec)
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.monoFix_least)
  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.nat_iterate_unique
end

end DomainTheory.NeighbourhoodSystems.NeighborhoodSystem
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace NeighborhoodSystem

theorem chainUnion_le (C : Set V.Element) (hne : C.Nonempty) (hchain : IsChain (· ≤ ·) C)
    {y : V.Element} (hy : ∀ x ∈ C, x ≤ y) : V.chainUnion C hne hchain ≤ y := by
  rintro Z ⟨x, hxC, hxZ⟩
  exact hy x hxC Z hxZ

end NeighborhoodSystem
end
end DomainTheory.NeighbourhoodSystems
end

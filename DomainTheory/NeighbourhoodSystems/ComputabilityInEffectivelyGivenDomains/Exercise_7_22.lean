module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem_4_2
public import Mathlib.Computability.EpsilonNFA
public import Mathlib.Data.Fintype.Option

public import Mathlib.Logic.Equiv.List
public import Mathlib.Data.Fintype.Prod

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
namespace Exercise722
open NeighborhoodSystem ApproximableMap

section

def concat (X Y : Set (List Bool)) : Set (List Bool) := {w | ∃ a ∈ X, ∃ b ∈ Y, a ++ b = w}
end

section

inductive InS : Set (List Bool) → Prop
  | univ : InS Set.univ
  | singleton (σ : List Bool) : InS {σ}
  | mul {X Y : Set (List Bool)} : InS X → InS Y → InS (concat X Y)
  | inter {X Y : Set (List Bool)} : InS X → InS Y → (X ∩ Y).Nonempty → InS (X ∩ Y)
end

section
@[simp] theorem mem_concat {X Y : Set (List Bool)} {w : List Bool} :
    w ∈ concat X Y ↔ ∃ a ∈ X, ∃ b ∈ Y, a ++ b = w := Iff.rfl
end

section

theorem Ssys_master_mem : InS Set.univ := InS.univ
end

section

theorem Ssys_master_nonempty : (Set.univ : Set (List Bool)).Nonempty := by
  exact ⟨[], Set.mem_univ []⟩
end

section

theorem Ssys_sub_master {X : Set (List Bool)} (_h : InS X) : X ⊆ Set.univ :=
  Set.subset_univ _
end

section

theorem concat_mono {X X' Y Y' : Set (List Bool)} (hX : X ⊆ X') (hY : Y ⊆ Y') :
    concat X Y ⊆ concat X' Y' := by
  rintro w ⟨a, ha, b, hb, rfl⟩; exact ⟨a, hX ha, b, hY hb, rfl⟩
end

section

theorem concat_nonempty {X Y : Set (List Bool)} (hX : X.Nonempty) (hY : Y.Nonempty) :
    (concat X Y).Nonempty := by
  obtain ⟨a, ha⟩ := hX
  obtain ⟨b, hb⟩ := hY
  exact ⟨a ++ b, a, ha, b, hb, rfl⟩
end

section

theorem InS.nonempty {X : Set (List Bool)} (h : InS X) : X.Nonempty := by
  induction h with
  | univ => exact ⟨[], trivial⟩
  | singleton σ => exact ⟨σ, rfl⟩
  | mul _ _ ihX ihY => exact concat_nonempty ihX ihY
  | inter _ _ hne _ _ => exact hne
end

section

theorem Ssys_inter_mem {X Y Z : Set (List Bool)}
    (hX : InS X) (hY : InS Y) (hZ : InS Z) (hZsub : Z ⊆ X ∩ Y) : InS (X ∩ Y) :=
  InS.inter hX hY (hZ.nonempty.mono hZsub)
end

end Exercise722
end DomainTheory.NeighbourhoodSystems

section
namespace DomainTheory.NeighbourhoodSystems
namespace Exercise722
open NeighborhoodSystem ApproximableMap
section

def Ssys : NeighborhoodSystem (List Bool) where
  mem := InS
  master := Set.univ
  master_nonempty := Ssys_master_nonempty
  master_mem := Ssys_master_mem
  inter_mem := Ssys_inter_mem
  sub_master := Ssys_sub_master
end

section
@[simp] theorem Ssys_mem {X : Set (List Bool)} : Ssys.mem X ↔ InS X := Iff.rfl
end

section

def mulElem (x y : Ssys.Element) : Ssys.Element where
  mem Z := InS Z ∧ ∃ X, x.mem X ∧ ∃ Y, y.mem Y ∧ concat X Y ⊆ Z
  sub h := h.1
  master_mem :=
    ⟨InS.univ, Set.univ, x.master_mem, Set.univ, y.master_mem, Set.subset_univ _⟩
  inter_mem := by
    rintro Z1 Z2 ⟨hZ1, X1, hX1, Y1, hY1, hsub1⟩ ⟨hZ2, X2, hX2, Y2, hY2, hsub2⟩
    have hXi : x.mem (X1 ∩ X2) := x.inter_mem hX1 hX2
    have hYi : y.mem (Y1 ∩ Y2) := y.inter_mem hY1 hY2
    have hcsub : concat (X1 ∩ X2) (Y1 ∩ Y2) ⊆ Z1 ∩ Z2 := by
      intro w hw
      exact ⟨hsub1 (concat_mono Set.inter_subset_left Set.inter_subset_left hw),
             hsub2 (concat_mono Set.inter_subset_right Set.inter_subset_right hw)⟩
    have hne : (Z1 ∩ Z2).Nonempty :=
      (concat_nonempty (x.sub hXi).nonempty (y.sub hYi).nonempty).mono hcsub
    exact ⟨InS.inter hZ1 hZ2 hne, X1 ∩ X2, hXi, Y1 ∩ Y2, hYi, hcsub⟩
  up_mem := by
    rintro Z W ⟨_, X, hX, Y, hY, hsub⟩ hW hZW
    exact ⟨hW, X, hX, Y, hY, hsub.trans hZW⟩
end

section
@[simp] theorem mem_mulElem {x y : Ssys.Element} {Z : Set (List Bool)} :
    (mulElem x y).mem Z ↔ InS Z ∧ ∃ X, x.mem X ∧ ∃ Y, y.mem Y ∧ concat X Y ⊆ Z := Iff.rfl
end

section

def emb (σ : List Bool) : Ssys.Element where
  mem X := InS X ∧ σ ∈ X
  sub h := h.1
  master_mem := ⟨InS.univ, Set.mem_univ σ⟩
  inter_mem := by
    rintro X Y ⟨hX, hσX⟩ ⟨hY, hσY⟩
    exact ⟨InS.inter hX hY ⟨σ, hσX, hσY⟩, hσX, hσY⟩
  up_mem := by
    rintro X Y ⟨_, hσ⟩ hY hsub
    exact ⟨hY, hsub hσ⟩
end

section
@[simp] theorem mem_emb {σ : List Bool} {X : Set (List Bool)} :
    (emb σ).mem X ↔ InS X ∧ σ ∈ X := Iff.rfl
end

section

def prependMap (σ : List Bool) : ApproximableMap Ssys Ssys where
  rel Y Z := InS Y ∧ InS Z ∧ concat {σ} Y ⊆ Z
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨InS.univ, InS.univ, Set.subset_univ _⟩
  inter_right := by
    rintro Y Z Z' ⟨hY, hZ, hsub⟩ ⟨_, hZ', hsub'⟩
    have hcsub : concat {σ} Y ⊆ Z ∩ Z' := Set.subset_inter hsub hsub'
    have hne : (Z ∩ Z').Nonempty :=
      (concat_nonempty (Set.singleton_nonempty σ) hY.nonempty).mono hcsub
    exact ⟨hY, InS.inter hZ hZ' hne, hcsub⟩
  mono := by
    rintro Y Y' Z Z' ⟨_, hZ, hsub⟩ hYY' hZZ' hY' hZ'
    exact ⟨hY', hZ', (concat_mono (Set.Subset.refl _) hYY').trans (hsub.trans hZZ')⟩
end

section

def repeatWord (w : List Bool) : ℕ → List Bool
  | 0 => []
  | n + 1 => w ++ repeatWord w n
end

section
@[simp] theorem repeatWord_zero (w : List Bool) : repeatWord w 0 = [] := rfl
end

section

def powerLang (w : List Bool) : Set (List Bool) :=
  {u | ∃ n, repeatWord w n = u}
end

section
@[simp] theorem mem_powerLang {w u : List Bool} :
    u ∈ powerLang w ↔ ∃ n, repeatWord w n = u := Iff.rfl
end

section

def streamArrow (σ : List Bool) : Ssys.Element := (prependMap σ).fixElement
end

section

def streamElemMem (w : List Bool) (Z : Set (List Bool)) : Prop :=
  InS Z ∧ ∀ n, repeatWord w n ∈ Z
end

section

def streamElem (w : List Bool) : Ssys.Element where
  mem Z := streamElemMem w Z
  sub h := h.1
  master_mem := ⟨InS.univ, fun n => Set.mem_univ (repeatWord w n)⟩
  inter_mem := by
    intro X Y hX hY
    obtain ⟨hXIn, hXw⟩ := hX
    obtain ⟨hYIn, hYw⟩ := hY
    exact ⟨InS.inter hXIn hYIn ⟨repeatWord w 0, hXw 0, hYw 0⟩, fun n => ⟨hXw n, hYw n⟩⟩
  up_mem := by
    intro X Y hX hInSY hsub
    obtain ⟨_hXIn, hXw⟩ := hX
    exact ⟨hInSY, fun n => hsub (hXw n)⟩
end

section

theorem append_mem_concat {X Y : Set (List Bool)} {a b : List Bool} (ha : a ∈ X) (hb : b ∈ Y) :
    a ++ b ∈ concat X Y := ⟨a, ha, b, hb, rfl⟩

theorem concat_assoc (X Y Z : Set (List Bool)) :
    concat (concat X Y) Z = concat X (concat Y Z) := by
  ext w
  constructor
  · rintro ⟨ab, ⟨a, ha, b, hb, rfl⟩, c, hc, rfl⟩
    exact ⟨a, ha, b ++ c, ⟨b, hb, c, hc, rfl⟩, by rw [List.append_assoc]⟩
  · rintro ⟨a, ha, bc, ⟨b, hb, c, hc, rfl⟩, rfl⟩
    exact ⟨a ++ b, ⟨a, ha, b, hb, rfl⟩, c, hc, by rw [List.append_assoc]⟩

theorem mulElem_assoc (x y z : Ssys.Element) :
    mulElem (mulElem x y) z = mulElem x (mulElem y z) := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro ⟨hW, P, ⟨_, X, hX, Y, hY, hXY⟩, Z, hZ, hPZ⟩
    refine ⟨hW, X, hX, concat Y Z, ⟨InS.mul (y.sub hY) (z.sub hZ), Y, hY, Z, hZ,
      Set.Subset.refl _⟩, ?_⟩
    rw [← concat_assoc]
    exact (concat_mono hXY (Set.Subset.refl _)).trans hPZ
  · rintro ⟨hW, X, hX, Q, ⟨_, Y, hY, Z, hZ, hYZ⟩, hXQ⟩
    refine ⟨hW, concat X Y, ⟨InS.mul (x.sub hX) (y.sub hY), X, hX, Y, hY,
      Set.Subset.refl _⟩, Z, hZ, ?_⟩
    rw [concat_assoc]
    exact (concat_mono (Set.Subset.refl _) hYZ).trans hXQ

theorem repeatWord_add (w : List Bool) (a b : ℕ) :
    repeatWord w (a + b) = repeatWord w a ++ repeatWord w b := by
  induction a with
  | zero => simp [repeatWord]
  | succ a ih =>
      simp only [Nat.succ_add, repeatWord]
      rw [ih, List.append_assoc]

theorem repeatWord_eq_empty (w : List Bool) (n : ℕ) (hw : w = []) :
    repeatWord w n = [] := by
  subst hw
  induction n with
  | zero => rfl
  | succ n ih => simp [repeatWord, ih]

theorem InS_powerLang_empty : InS (powerLang []) := by
  have h : powerLang [] = {[]} := by
    ext u
    simp only [mem_powerLang, Set.mem_singleton_iff]
    constructor
    · rintro ⟨n, hn⟩; exact hn.symm.trans (repeatWord_eq_empty [] n rfl)
    · intro hu; subst hu; exact ⟨0, rfl⟩
  simpa [h] using InS.singleton []

@[simp] theorem mem_streamElem {w : List Bool} {Z : Set (List Bool)} :
    (streamElem w).mem Z ↔ streamElemMem w Z := Iff.rfl

theorem streamElem_powers_of_mul (w : List Bool) (Z : Set (List Bool))
    (h : (mulElem (streamElem w) (streamElem w)).mem Z) :
    streamElemMem w Z := by
  obtain ⟨hZ, X, hX, Y, hY, hsub⟩ := h
  obtain ⟨_hXIn, hXw⟩ := hX
  obtain ⟨_hYIn, hYw⟩ := hY
  refine ⟨hZ, fun n => ?_⟩
  have h1 := hsub (append_mem_concat (hXw n) (hYw 0))
  simpa [repeatWord_zero, List.append_nil] using h1

theorem streamElem_mul_self_mem (w : List Bool) (Z : Set (List Bool))
    (h : streamElemMem w Z) (hPL : InS (powerLang w)) :
    (mulElem (streamElem w) (streamElem w)).mem Z := by
  refine ⟨h.1, powerLang w, ⟨hPL, fun n => ⟨n, rfl⟩⟩, powerLang w, ⟨hPL, fun n => ⟨n, rfl⟩⟩, ?_⟩
  intro u hu
  obtain ⟨a, ⟨m, hm⟩, b, ⟨n, hn⟩, rfl⟩ := hu
  simpa [hm, hn, repeatWord_add] using h.2 (m + n)

theorem streamElem_idempotent (w : List Bool) (hPL : InS (powerLang w)) :
    mulElem (streamElem w) (streamElem w) = streamElem w := by
  apply NeighborhoodSystem.Element.ext
  intro Z
  exact ⟨streamElem_powers_of_mul w Z, fun h => streamElem_mul_self_mem w Z h hPL⟩

example : mulElem (streamElem []) (streamElem []) = streamElem [] :=
  streamElem_idempotent [] InS_powerLang_empty

example (σ : List Bool) (Z : Set (List Bool)) :
    (mulElem (streamElem σ) (streamElem σ)).mem Z → streamElemMem σ Z :=
  streamElem_powers_of_mul σ Z

example (σ : List Bool) (h : InS (powerLang σ)) :
    mulElem (mulElem (streamElem σ) (streamElem σ)) (streamElem σ) = streamElem σ := by
  rw [mulElem_assoc, streamElem_idempotent σ h, streamElem_idempotent σ h]

example (σ : List Bool) (h : InS (powerLang (σ ++ [true]))) :
    mulElem (streamElem (σ ++ [true])) (streamElem (σ ++ [true])) =
      streamElem (σ ++ [true]) :=
  streamElem_idempotent (σ ++ [true]) h

example (h : InS (powerLang [false, true])) :
    mulElem
        (mulElem (streamElem [false, true]) (streamElem [false, true]))
        (mulElem (streamElem [false, true]) (streamElem [false, true])) =
      mulElem (streamElem [false, true]) (streamElem [false, true]) := by
  rw [streamElem_idempotent _ h, streamElem_idempotent _ h]
end

section

theorem Ssys_isPositive : Ssys.IsPositive := by
  intro X Y hX hY
  exact ⟨fun h => h.nonempty, fun h => InS.inter hX hY h⟩
end

section
theorem Ssys_master : Ssys.master = Set.univ := rfl
end

section

theorem concat_singleton (a b : List Bool) : concat {a} {b} = {a ++ b} := by
  ext w
  simp only [mem_concat, Set.mem_singleton_iff]
  constructor
  · rintro ⟨a', rfl, b', rfl, rfl⟩; rfl
  · rintro rfl; exact ⟨a, rfl, b, rfl, rfl⟩
end

section

theorem emb_injective : Function.Injective emb := by
  intro σ τ h
  have hmem : (emb τ).mem {σ} := h ▸ (⟨InS.singleton σ, rfl⟩ : (emb σ).mem {σ})
  exact (Set.mem_singleton_iff.mp hmem.2).symm
end

section

theorem emb_mul (σ τ : List Bool) : emb (σ ++ τ) = mulElem (emb σ) (emb τ) := by
  apply NeighborhoodSystem.Element.ext
  intro Z
  constructor
  · rintro ⟨hZ, hστ⟩
    refine ⟨hZ, {σ}, ⟨InS.singleton σ, rfl⟩, {τ}, ⟨InS.singleton τ, rfl⟩, ?_⟩
    rw [concat_singleton]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw; exact hστ
  · rintro ⟨hZ, X, ⟨_, hσX⟩, Y, ⟨_, hτY⟩, hsub⟩
    exact ⟨hZ, hsub (append_mem_concat hσX hτY)⟩
end

section

theorem mulElem_bot_le (y : Ssys.Element) : mulElem Ssys.bot y ≤ y := by
  rintro Z ⟨hInS, X, hX, Y, hY, hsub⟩
  rw [NeighborhoodSystem.mem_bot, Ssys_master] at hX
  subst hX
  refine y.up_mem hY hInS fun w hw => hsub ?_
  simpa using append_mem_concat (Set.mem_univ ([] : List Bool)) hw
end

section

theorem mulElem_mono_right (x : Ssys.Element) : Monotone (mulElem x) := by
  rintro y y' hyy' Z ⟨hInS, X, hX, Y, hY, hsub⟩
  exact ⟨hInS, X, hX, Y, hyy' Y hY, hsub⟩
end

section
theorem powerLang_concat (w : List Bool) :
    concat (powerLang w) (powerLang w) ⊆ powerLang w := by
  rintro u ⟨a, ⟨m, hm⟩, b, ⟨n, hn⟩, rfl⟩
  exact ⟨m + n, by rw [repeatWord_add, hm, hn]⟩
end

section

theorem prependMap_toElementMap (σ : List Bool) (y : Ssys.Element) :
    (prependMap σ).toElementMap y = mulElem (emb σ) y := by
  apply NeighborhoodSystem.Element.ext
  intro Z
  constructor
  · rintro ⟨Y, hY, hInSY, hInSZ, hsub⟩
    exact ⟨hInSZ, {σ}, ⟨InS.singleton σ, rfl⟩, Y, hY, hsub⟩
  · rintro ⟨hInSZ, X, ⟨_, hσX⟩, Y, hY, hsub⟩
    refine ⟨Y, hY, y.sub hY, hInSZ, ?_⟩
    exact (concat_mono (Set.singleton_subset_iff.mpr hσX) (Set.Subset.refl _)).trans hsub
end

section
theorem repeatWord_succ (w : List Bool) (n : ℕ) :
    repeatWord w (n + 1) = w ++ repeatWord w n := rfl
end

section

theorem streamArrow_eq (σ : List Bool) :
    mulElem (emb σ) (streamArrow σ) = streamArrow σ := by
  rw [← prependMap_toElementMap]
  exact toElementMap_fixElement (prependMap σ)
end

section

theorem prependMap_iterElem_mul_streamArrow_le (σ : List Bool) :
    ∀ n, mulElem ((prependMap σ).iterElem n) (streamArrow σ) ≤ streamArrow σ
  | 0 => by
      have h0 : (prependMap σ).iterElem 0 = Ssys.bot := by
        show (idMap Ssys).toElementMap Ssys.bot = Ssys.bot
        exact toElementMap_idMap Ssys.bot
      rw [h0]
      exact mulElem_bot_le (streamArrow σ)
  | n + 1 => by
      have hsucc : (prependMap σ).iterElem (n + 1) =
          mulElem (emb σ) ((prependMap σ).iterElem n) := by
        show ((prependMap σ).comp ((prependMap σ).iterMap n)).toElementMap Ssys.bot = _
        rw [toElementMap_comp]
        exact prependMap_toElementMap σ _
      rw [hsucc, mulElem_assoc]
      calc mulElem (emb σ) (mulElem ((prependMap σ).iterElem n) (streamArrow σ))
          ≤ mulElem (emb σ) (streamArrow σ) :=
            mulElem_mono_right (emb σ) (prependMap_iterElem_mul_streamArrow_le σ n)
        _ = streamArrow σ := streamArrow_eq σ
end

section

theorem streamArrow_le_mul_self (σ : List Bool) :
    streamArrow σ ≤ mulElem (streamArrow σ) (streamArrow σ) := by
  apply fixElement_le_of_toElementMap_le
  have heq : (prependMap σ).toElementMap (mulElem (streamArrow σ) (streamArrow σ)) =
      mulElem (streamArrow σ) (streamArrow σ) := by
    rw [prependMap_toElementMap, ← mulElem_assoc, streamArrow_eq]
  exact le_of_eq heq
end

section

theorem streamArrow_mul_self_le (σ : List Bool) :
    mulElem (streamArrow σ) (streamArrow σ) ≤ streamArrow σ := by
  rintro Z ⟨hInSZ, X, hX, Y, hY, hsub⟩
  obtain ⟨n, hn⟩ := (mem_fixElement (prependMap σ)).mp hX
  have hXn : ((prependMap σ).iterElem n).mem X := (mem_iterElem (prependMap σ) n).mpr hn
  exact prependMap_iterElem_mul_streamArrow_le σ n Z ⟨hInSZ, X, hXn, Y, hY, hsub⟩
end

section

theorem streamArrow_mul_self (σ : List Bool) :
    mulElem (streamArrow σ) (streamArrow σ) = streamArrow σ :=
  le_antisymm (streamArrow_mul_self_le σ) (streamArrow_le_mul_self σ)
end

end Exercise722
end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Exercise722
section
set_option linter.unusedVariables false

theorem example_722 : And
  (And
    (∀ (σ τ : List Bool),
      @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (List Bool)
          DomainTheory.NeighbourhoodSystems.Exercise722.Ssys)
        (DomainTheory.NeighbourhoodSystems.Exercise722.emb
          (@HAppend.hAppend (List Bool) (List Bool) (List Bool)
            (@instHAppendOfAppend (List Bool) (@List.instAppend Bool)) σ τ))
        (DomainTheory.NeighbourhoodSystems.Exercise722.mulElem (DomainTheory.NeighbourhoodSystems.Exercise722.emb σ)
          (DomainTheory.NeighbourhoodSystems.Exercise722.emb τ)))
    (∀
      (x y z :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (List Bool)
          DomainTheory.NeighbourhoodSystems.Exercise722.Ssys),
      @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (List Bool)
          DomainTheory.NeighbourhoodSystems.Exercise722.Ssys)
        (DomainTheory.NeighbourhoodSystems.Exercise722.mulElem
          (DomainTheory.NeighbourhoodSystems.Exercise722.mulElem x y) z)
        (DomainTheory.NeighbourhoodSystems.Exercise722.mulElem x
          (DomainTheory.NeighbourhoodSystems.Exercise722.mulElem y z))))
  (∀ (σ : List Bool),
    @Eq
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (List Bool)
        DomainTheory.NeighbourhoodSystems.Exercise722.Ssys)
      (DomainTheory.NeighbourhoodSystems.Exercise722.mulElem
        (DomainTheory.NeighbourhoodSystems.Exercise722.streamArrow σ)
        (DomainTheory.NeighbourhoodSystems.Exercise722.streamArrow σ))
      (DomainTheory.NeighbourhoodSystems.Exercise722.streamArrow σ)) :=
  @And.intro
  (And
    (∀ (σ τ : List Bool),
      @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (List Bool)
          DomainTheory.NeighbourhoodSystems.Exercise722.Ssys)
        (DomainTheory.NeighbourhoodSystems.Exercise722.emb
          (@HAppend.hAppend (List Bool) (List Bool) (List Bool)
            (@instHAppendOfAppend (List Bool) (@List.instAppend Bool)) σ τ))
        (DomainTheory.NeighbourhoodSystems.Exercise722.mulElem (DomainTheory.NeighbourhoodSystems.Exercise722.emb σ)
          (DomainTheory.NeighbourhoodSystems.Exercise722.emb τ)))
    (∀
      (x y z :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (List Bool)
          DomainTheory.NeighbourhoodSystems.Exercise722.Ssys),
      @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (List Bool)
          DomainTheory.NeighbourhoodSystems.Exercise722.Ssys)
        (DomainTheory.NeighbourhoodSystems.Exercise722.mulElem
          (DomainTheory.NeighbourhoodSystems.Exercise722.mulElem x y) z)
        (DomainTheory.NeighbourhoodSystems.Exercise722.mulElem x
          (DomainTheory.NeighbourhoodSystems.Exercise722.mulElem y z))))
  (∀ (σ : List Bool),
    @Eq
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (List Bool)
        DomainTheory.NeighbourhoodSystems.Exercise722.Ssys)
      (DomainTheory.NeighbourhoodSystems.Exercise722.mulElem
        (DomainTheory.NeighbourhoodSystems.Exercise722.streamArrow σ)
        (DomainTheory.NeighbourhoodSystems.Exercise722.streamArrow σ))
      (DomainTheory.NeighbourhoodSystems.Exercise722.streamArrow σ))
  (@And.intro
    (∀ (σ τ : List Bool),
      @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (List Bool)
          DomainTheory.NeighbourhoodSystems.Exercise722.Ssys)
        (DomainTheory.NeighbourhoodSystems.Exercise722.emb
          (@HAppend.hAppend (List Bool) (List Bool) (List Bool)
            (@instHAppendOfAppend (List Bool) (@List.instAppend Bool)) σ τ))
        (DomainTheory.NeighbourhoodSystems.Exercise722.mulElem (DomainTheory.NeighbourhoodSystems.Exercise722.emb σ)
          (DomainTheory.NeighbourhoodSystems.Exercise722.emb τ)))
    (∀
      (x y z :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (List Bool)
          DomainTheory.NeighbourhoodSystems.Exercise722.Ssys),
      @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (List Bool)
          DomainTheory.NeighbourhoodSystems.Exercise722.Ssys)
        (DomainTheory.NeighbourhoodSystems.Exercise722.mulElem
          (DomainTheory.NeighbourhoodSystems.Exercise722.mulElem x y) z)
        (DomainTheory.NeighbourhoodSystems.Exercise722.mulElem x
          (DomainTheory.NeighbourhoodSystems.Exercise722.mulElem y z)))
    DomainTheory.NeighbourhoodSystems.Exercise722.emb_mul DomainTheory.NeighbourhoodSystems.Exercise722.mulElem_assoc)
  DomainTheory.NeighbourhoodSystems.Exercise722.streamArrow_mul_self
end

end DomainTheory.NeighbourhoodSystems.Exercise722
namespace DomainTheory.NeighbourhoodSystems
namespace Exercise722
open NeighborhoodSystem ApproximableMap

section

theorem streamArrow_containsZero_pow_four :
    mulElem
        (mulElem (streamArrow [false, true]) (streamArrow [false, true]))
        (mulElem (streamArrow [false, true]) (streamArrow [false, true]))
      = mulElem (streamArrow [false, true]) (streamArrow [false, true]) := by
  rw [streamArrow_mul_self, streamArrow_mul_self]
end

section

theorem streamArrow_mul_self_append_true (σ : List Bool) :
    mulElem (streamArrow (σ ++ [true])) (streamArrow (σ ++ [true])) =
      streamArrow (σ ++ [true]) :=
  streamArrow_mul_self (σ ++ [true])
end

section

theorem streamArrow_mul_self_self (σ : List Bool) :
    mulElem (mulElem (streamArrow σ) (streamArrow σ)) (streamArrow σ) = streamArrow σ := by
  rw [streamArrow_mul_self, streamArrow_mul_self]
end

section

inductive SExpr : Type
  | sigma : SExpr
  | single : List Bool → SExpr
  | cat : SExpr → SExpr → SExpr
  | cap : SExpr → SExpr → SExpr
  deriving DecidableEq
end

section

def sexprOfNatFuel : ℕ → ℕ → Option SExpr
  | 0, _ => none
  | fuel + 1, n =>
    match n.unpair.1 with
    | 0 => some .sigma
    | 1 => (Encodable.decode n.unpair.2).map SExpr.single
    | 2 =>
      match sexprOfNatFuel fuel n.unpair.2.unpair.1, sexprOfNatFuel fuel n.unpair.2.unpair.2 with
      | some a, some b => some (.cat a b)
      | _, _ => none
    | 3 =>
      match sexprOfNatFuel fuel n.unpair.2.unpair.1, sexprOfNatFuel fuel n.unpair.2.unpair.2 with
      | some a, some b => some (.cap a b)
      | _, _ => none
    | _ => none
end

section
def sexprOfNat (n : ℕ) : Option SExpr := sexprOfNatFuel (n + 1) n
end

section
def sexprToNat : SExpr → ℕ
  | .sigma => Nat.pair 0 0
  | .single σ => Nat.pair 1 (Encodable.encode σ)
  | .cat a b => Nat.pair 2 (Nat.pair (sexprToNat a) (sexprToNat b))
  | .cap a b => Nat.pair 3 (Nat.pair (sexprToNat a) (sexprToNat b))
end

section
theorem snd_lt_pair_of_pos_fst {a b : ℕ} (ha : 0 < a) : b < Nat.pair a b := by
  rw [Nat.pair]
  split_ifs with h
  · have hb : 0 < b := Nat.lt_trans ha h
    have hbb : b ≤ b * b := by
      calc
        b = 1 * b := (Nat.one_mul b).symm
        _ ≤ b * b := Nat.mul_le_mul_right b (Nat.succ_le_of_lt hb)
    have : b * b < b * b + a := Nat.lt_add_of_pos_right ha
    omega
  · have : 0 < a * a + a := by
      have : a ≤ a * a + a := Nat.le_add_left _ _
      omega
    omega
end

section
theorem sexprOfNatFuel_sexprToNat (e : SExpr) :
    ∀ fuel, sexprToNat e < fuel → sexprOfNatFuel fuel (sexprToNat e) = some e := by
  induction e with
  | sigma =>
    intro fuel hfuel
    cases fuel with
    | zero => omega
    | succ fuel => simp [sexprToNat, sexprOfNatFuel, Nat.unpair_pair]
  | single σ =>
    intro fuel hfuel
    cases fuel with
    | zero => omega
    | succ fuel => simp [sexprToNat, sexprOfNatFuel, Nat.unpair_pair, Encodable.encodek]
  | cat a b iha ihb =>
    intro fuel hfuel
    cases fuel with
    | zero => omega
    | succ fuel =>
      have ha : sexprToNat a < fuel := by
        have hinner : sexprToNat a ≤ Nat.pair (sexprToNat a) (sexprToNat b) := Nat.left_le_pair _ _
        have houter : Nat.pair (sexprToNat a) (sexprToNat b) < sexprToNat (.cat a b) := by
          simpa [sexprToNat] using snd_lt_pair_of_pos_fst (a := 2) (b := Nat.pair (sexprToNat a) (sexprToNat b)) (by omega)
        omega
      have hb : sexprToNat b < fuel := by
        have hinner : sexprToNat b ≤ Nat.pair (sexprToNat a) (sexprToNat b) := Nat.right_le_pair _ _
        have houter : Nat.pair (sexprToNat a) (sexprToNat b) < sexprToNat (.cat a b) := by
          simpa [sexprToNat] using snd_lt_pair_of_pos_fst (a := 2) (b := Nat.pair (sexprToNat a) (sexprToNat b)) (by omega)
        omega
      simp [sexprToNat, sexprOfNatFuel, Nat.unpair_pair, iha _ ha, ihb _ hb]
  | cap a b iha ihb =>
    intro fuel hfuel
    cases fuel with
    | zero => omega
    | succ fuel =>
      have ha : sexprToNat a < fuel := by
        have hinner : sexprToNat a ≤ Nat.pair (sexprToNat a) (sexprToNat b) := Nat.left_le_pair _ _
        have houter : Nat.pair (sexprToNat a) (sexprToNat b) < sexprToNat (.cap a b) := by
          simpa [sexprToNat] using snd_lt_pair_of_pos_fst (a := 3) (b := Nat.pair (sexprToNat a) (sexprToNat b)) (by omega)
        omega
      have hb : sexprToNat b < fuel := by
        have hinner : sexprToNat b ≤ Nat.pair (sexprToNat a) (sexprToNat b) := Nat.right_le_pair _ _
        have houter : Nat.pair (sexprToNat a) (sexprToNat b) < sexprToNat (.cap a b) := by
          simpa [sexprToNat] using snd_lt_pair_of_pos_fst (a := 3) (b := Nat.pair (sexprToNat a) (sexprToNat b)) (by omega)
        omega
      simp [sexprToNat, sexprOfNatFuel, Nat.unpair_pair, iha _ ha, ihb _ hb]
end

section
instance : Encodable SExpr where
  encode := sexprToNat
  decode := sexprOfNat
  encodek e := sexprOfNatFuel_sexprToNat e (sexprToNat e + 1) (Nat.lt_succ_self _)
end

section

def denote : SExpr → Set (List Bool)
  | .sigma => Set.univ
  | .single σ => {σ}
  | .cat a b => concat (denote a) (denote b)
  | .cap a b => denote a ∩ denote b
end

section
@[simp] theorem denote_sigma : denote .sigma = Set.univ := rfl
end

section
@[simp] theorem denote_single (σ : List Bool) : denote (.single σ) = {σ} := rfl
end

section
@[simp] theorem denote_cat (a b : SExpr) : denote (.cat a b) = concat (denote a) (denote b) := rfl
end

section
@[simp] theorem denote_cap (a b : SExpr) : denote (.cap a b) = denote a ∩ denote b := rfl
end

section

def matchesB : SExpr → List Bool → Bool
  | .sigma, _ => true
  | .single σ, w => decide (w = σ)
  | .cat a b, w => (List.range (w.length + 1)).any (fun i => matchesB a (w.take i) && matchesB b (w.drop i))
  | .cap a b, w => matchesB a w && matchesB b w
end

section

theorem mem_concat_iff_split {X Y : Set (List Bool)} {w : List Bool} :
    w ∈ concat X Y ↔ ∃ i, i ≤ w.length ∧ w.take i ∈ X ∧ w.drop i ∈ Y := by
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨a.length, by simp, ?_, ?_⟩
    · rw [List.take_left]; exact ha
    · rw [List.drop_left]; exact hb
  · rintro ⟨i, _, hpre, hsuf⟩
    exact ⟨w.take i, hpre, w.drop i, hsuf, w.take_append_drop i⟩
end

section

theorem matchesB_iff (e : SExpr) (w : List Bool) : matchesB e w = true ↔ w ∈ denote e := by
  induction e generalizing w with
  | sigma => simp [matchesB]
  | single σ => simp [matchesB]
  | cat a b iha ihb =>
    rw [denote_cat, mem_concat_iff_split]
    simp only [matchesB, List.any_eq_true, List.mem_range, Bool.and_eq_true]
    constructor
    · rintro ⟨i, hi, ha, hb⟩
      exact ⟨i, Nat.lt_succ_iff.mp hi, (iha _).mp ha, (ihb _).mp hb⟩
    · rintro ⟨i, hi, ha, hb⟩
      exact ⟨i, Nat.lt_succ_iff.mpr hi, (iha _).mpr ha, (ihb _).mpr hb⟩
  | cap a b iha ihb =>
    simp only [matchesB, Bool.and_eq_true, denote_cap, Set.mem_inter_iff]
    rw [iha, ihb]
end

section

instance decidableMemDenote (e : SExpr) : DecidablePred (· ∈ denote e) :=
  fun w => decidable_of_iff (matchesB e w = true) (matchesB_iff e w)
end

section
instance : Countable SExpr := inferInstance
end

section

def emptyExpr : SExpr := .cap (.single [false]) (.single [true])
end

section
@[simp] theorem denote_emptyExpr : denote emptyExpr = (∅ : Set (List Bool)) := by
  ext w
  simp only [emptyExpr, denote_cap, denote_single, Set.mem_inter_iff, Set.mem_singleton_iff,
    Set.mem_empty_iff_false, iff_false, not_and]
  rintro rfl
  decide
end

section

def containsZero : SExpr := .cat .sigma (.cat (.single [false]) .sigma)
end

section

theorem InS_denote_of_nonempty : ∀ {e : SExpr}, (denote e).Nonempty → InS (denote e)
  | .sigma, _ => InS.univ
  | .single σ, _ => InS.singleton σ
  | .cat a b, h => by
    rw [denote_cat] at h ⊢
    obtain ⟨w, x, hx, y, hy, _⟩ := h
    exact InS.mul (InS_denote_of_nonempty ⟨x, hx⟩) (InS_denote_of_nonempty ⟨y, hy⟩)
  | .cap a b, h => by
    rw [denote_cap] at h ⊢
    have ha : (denote a).Nonempty := h.mono Set.inter_subset_left
    have hb : (denote b).Nonempty := h.mono Set.inter_subset_right
    exact InS.inter (InS_denote_of_nonempty ha) (InS_denote_of_nonempty hb) h
end

section

theorem InS_exists_denote {X : Set (List Bool)} (h : InS X) : ∃ e : SExpr, denote e = X := by
  induction h with
  | univ => exact ⟨.sigma, rfl⟩
  | singleton σ => exact ⟨.single σ, rfl⟩
  | mul _ _ iha ihb =>
    obtain ⟨ea, rfl⟩ := iha
    obtain ⟨eb, rfl⟩ := ihb
    exact ⟨.cat ea eb, rfl⟩
  | inter _ _ _ iha ihb =>
    obtain ⟨ea, rfl⟩ := iha
    obtain ⟨eb, rfl⟩ := ihb
    exact ⟨.cap ea eb, rfl⟩
end

section

theorem denote_catSigmaSigma : denote (.cat .sigma .sigma) = denote .sigma := by
  ext w
  simp only [denote_cat, denote_sigma, mem_concat, Set.mem_univ, iff_true]
  exact ⟨[], trivial, w, trivial, rfl⟩
end

section

theorem empty_iff_equiv_emptyExpr (a b : SExpr) :
    denote (.cap a b) = (∅ : Set (List Bool)) ↔ denote (.cap a b) = denote emptyExpr := by
  rw [denote_emptyExpr]
end

section
theorem inS_eq_range_denote : {X | InS X} = denote '' {e | (denote e).Nonempty} := by
  ext X
  simp only [Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · intro h
    obtain ⟨e, he⟩ := InS_exists_denote h
    exact ⟨e, by rw [he]; exact h.nonempty, he⟩
  · rintro ⟨e, hne, rfl⟩
    exact InS_denote_of_nonempty hne
end

section

theorem inS_iff_exists_denote {X : Set (List Bool)} :
    InS X ↔ ∃ e : SExpr, denote e = X ∧ X.Nonempty := by
  constructor
  · intro h
    obtain ⟨e, he⟩ := InS_exists_denote h
    exact ⟨e, he, h.nonempty⟩
  · rintro ⟨e, rfl, hne⟩
    exact InS_denote_of_nonempty hne
end

section

theorem interEq_iff (a b k : SExpr) :
    denote a ∩ denote b = denote k ↔ denote (.cap a b) = denote k := by
  rw [denote_cap]
end

section

theorem mem_denote_sigma (w : List Bool) : w ∈ denote .sigma := Set.mem_univ w
end

section

theorem sigma_ne_containsZero : denote .sigma ≠ denote containsZero := by
  intro h
  have h1 : ([true] : List Bool) ∈ denote .sigma := mem_denote_sigma _
  rw [h] at h1
  exact absurd h1 (by decide)
end

end Exercise722
end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Exercise722
section
set_option linter.unusedVariables false

theorem example_722_regular : @Ne (Set (List Bool))
  (DomainTheory.NeighbourhoodSystems.Exercise722.denote DomainTheory.NeighbourhoodSystems.Exercise722.SExpr.sigma)
  (DomainTheory.NeighbourhoodSystems.Exercise722.denote DomainTheory.NeighbourhoodSystems.Exercise722.containsZero) :=
  DomainTheory.NeighbourhoodSystems.Exercise722.sigma_ne_containsZero
end

end DomainTheory.NeighbourhoodSystems.Exercise722
namespace DomainTheory.NeighbourhoodSystems
namespace Exercise722
open scoped Computability
open Sum Set

section
variable {σ₁ σ₂ : Type}

def catEps (M₁ : NFA Bool σ₁) (M₂ : NFA Bool σ₂) : εNFA Bool (σ₁ ⊕ σ₂) where
  step s a :=
    match s, a with
    | inl s, some c => inl '' M₁.step s c
    | inl s, none   => {t | s ∈ M₁.accept ∧ t ∈ inr '' M₂.start}
    | inr s, some c => inr '' M₂.step s c
    | inr _, none   => ∅
  start := inl '' M₁.start
  accept := inr '' M₂.accept
end

section
variable {σ₁ σ₂ : Type}
variable (M₁ : NFA Bool σ₁) (M₂ : NFA Bool σ₂)

@[simp] theorem catEps_step_inl_some (s : σ₁) (c : Bool) :
    (catEps M₁ M₂).step (inl s) (some c) = inl '' M₁.step s c := rfl
@[simp] theorem catEps_step_inl_none (s : σ₁) :
    (catEps M₁ M₂).step (inl s) none = {t | s ∈ M₁.accept ∧ t ∈ inr '' M₂.start} := rfl
@[simp] theorem catEps_step_inr_some (s : σ₂) (c : Bool) :
    (catEps M₁ M₂).step (inr s) (some c) = inr '' M₂.step s c := rfl
@[simp] theorem catEps_step_inr_none (s : σ₂) :
    (catEps M₁ M₂).step (inr s) none = ∅ := rfl
@[simp] theorem catEps_start : (catEps M₁ M₂).start = inl '' M₁.start := rfl
@[simp] theorem catEps_accept : (catEps M₁ M₂).accept = inr '' M₂.accept := rfl

example [Fintype σ₁] [Fintype σ₂] : Fintype (σ₁ ⊕ σ₂) := inferInstance

theorem catEps_mem_εClosure_iff (T : Set (σ₁ ⊕ σ₂)) (s : σ₁ ⊕ σ₂) :
    s ∈ (catEps M₁ M₂).εClosure T ↔
      s ∈ T ∨ ((∃ q ∈ M₁.accept, (inl q : σ₁ ⊕ σ₂) ∈ T) ∧ s ∈ inr '' M₂.start) := by
  constructor
  · intro h
    induction h using εNFA.εClosure_induction with
    | base x hx => exact Or.inl hx
    | step x y hyx _hclos ih =>

      cases x with
      | inl q =>
        rcases ih with hT | ⟨_, hmem⟩
        · simp only [catEps_step_inl_none, mem_ofPred_eq] at hyx
          exact Or.inr ⟨⟨q, hyx.1, hT⟩, hyx.2⟩
        · obtain ⟨w, _, hw⟩ := hmem; exact absurd hw.symm (by simp)
      | inr q => simp only [catEps_step_inr_none] at hyx; exact absurd hyx (by simp)
  · rintro (hs | ⟨⟨q, hq, hqT⟩, hs⟩)
    · exact (catEps M₁ M₂).subset_εClosure T hs
    · obtain ⟨t, ht, rfl⟩ := hs
      have hbase : (inl q : σ₁ ⊕ σ₂) ∈ (catEps M₁ M₂).εClosure T :=
        (catEps M₁ M₂).subset_εClosure T hqT
      refine (catEps M₁ M₂).mem_εClosure_of_mem_step ?_ hbase
      simp only [catEps_step_inl_none, mem_ofPred_eq]
      exact ⟨hq, t, ht, rfl⟩

theorem catEps_mem_eval_iff (x : List Bool) (s : σ₁ ⊕ σ₂) :
    s ∈ (catEps M₁ M₂).eval x ↔
      (∃ s₁, s = inl s₁ ∧ s₁ ∈ M₁.eval x) ∨
      (∃ t, s = inr t ∧ ∃ u v, x = u ++ v ∧ u ∈ M₁.accepts ∧ t ∈ M₂.eval v) := by
  induction x using List.reverseRecOn generalizing s with
  | nil =>
    show s ∈ (catEps M₁ M₂).εClosure (catEps M₁ M₂).start ↔ _
    rw [catEps_start, catEps_mem_εClosure_iff]
    constructor
    · rintro (hs | ⟨⟨q, hq, hqs⟩, hs⟩)
      · obtain ⟨s₁, hs₁, rfl⟩ := hs
        exact Or.inl ⟨s₁, rfl, hs₁⟩
      · obtain ⟨t, ht, rfl⟩ := hs
        refine Or.inr ⟨t, rfl, [], [], rfl, ?_, ht⟩
        obtain ⟨q', hq', hqq⟩ := hqs
        cases hqq
        exact ⟨q, hq, hq'⟩
    · rintro (⟨s₁, rfl, hs₁⟩ | ⟨t, rfl, u, v, hx, hu, hv⟩)
      · exact Or.inl ⟨s₁, hs₁, rfl⟩
      · obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hx.symm
        obtain ⟨q, hq, hqstart⟩ := hu
        exact Or.inr ⟨⟨q, hq, q, hqstart, rfl⟩, t, hv, rfl⟩
  | append_singleton x a ih =>
    rw [εNFA.eval_append_singleton, εNFA.mem_stepSet_iff]
    constructor
    · rintro ⟨t, ht, hs⟩
      rw [ih] at ht
      rcases ht with ⟨s₁, rfl, hs₁⟩ | ⟨t₂, rfl, u, v, hx, hu, hv⟩
      ·
        rw [catEps_step_inl_some, catEps_mem_εClosure_iff] at hs
        rcases hs with hs | ⟨⟨q, hq, hqmem⟩, hs⟩
        ·
          obtain ⟨s', hs', rfl⟩ := hs
          exact Or.inl ⟨s', rfl, by rw [NFA.eval_append_singleton, NFA.mem_stepSet]; exact ⟨s₁, hs₁, hs'⟩⟩
        ·
          obtain ⟨q', hq', hqq⟩ := hqmem
          cases hqq
          obtain ⟨t', ht', rfl⟩ := hs
          refine Or.inr ⟨t', rfl, x ++ [a], [], (List.append_nil _).symm, ?_, ht'⟩
          rw [NFA.mem_accepts]
          refine ⟨q, hq, ?_⟩
          change q ∈ M₁.eval (x ++ [a])
          rw [NFA.eval_append_singleton, NFA.mem_stepSet]
          exact ⟨s₁, hs₁, hq'⟩
      ·
        rw [catEps_step_inr_some, catEps_mem_εClosure_iff] at hs
        rcases hs with hs | ⟨⟨q, _, hqmem⟩, _⟩
        · obtain ⟨t', ht', rfl⟩ := hs
          refine Or.inr ⟨t', rfl, u, v ++ [a], by rw [hx, List.append_assoc], hu, ?_⟩
          rw [NFA.eval_append_singleton, NFA.mem_stepSet]; exact ⟨t₂, hv, ht'⟩
        · exact absurd hqmem (by simp)
    · rintro (⟨s', rfl, hs'⟩ | ⟨t', rfl, u, v, hx, hu, hv⟩)
      ·
        rw [NFA.eval_append_singleton, NFA.mem_stepSet] at hs'
        obtain ⟨s₁, hs₁, hstep⟩ := hs'
        exact ⟨inl s₁, (ih (inl s₁)).mpr (Or.inl ⟨s₁, rfl, hs₁⟩),
          by rw [catEps_step_inl_some, catEps_mem_εClosure_iff]; exact Or.inl ⟨s', hstep, rfl⟩⟩
      ·
        rcases List.eq_nil_or_concat v with rfl | ⟨v', c, rfl⟩
        ·
          rw [List.append_nil] at hx; subst hx
          rw [NFA.mem_accepts] at hu
          obtain ⟨q, hq, hqe⟩ := hu
          change q ∈ M₁.eval (x ++ [a]) at hqe
          rw [NFA.eval_append_singleton, NFA.mem_stepSet] at hqe
          obtain ⟨s₁, hs₁, hstep⟩ := hqe
          refine ⟨inl s₁, (ih (inl s₁)).mpr (Or.inl ⟨s₁, rfl, hs₁⟩), ?_⟩
          rw [catEps_step_inl_some, catEps_mem_εClosure_iff]
          exact Or.inr ⟨⟨q, hq, q, hstep, rfl⟩, t', hv, rfl⟩
        ·
          rw [List.concat_eq_append] at hx hv
          rw [← List.append_assoc] at hx
          obtain ⟨hxe, hac⟩ := List.append_inj' hx rfl
          have hca : c = a := by simpa using hac.symm
          subst hca
          rw [NFA.eval_append_singleton, NFA.mem_stepSet] at hv
          obtain ⟨t₂, ht₂, hstep⟩ := hv
          refine ⟨inr t₂, (ih (inr t₂)).mpr (Or.inr ⟨t₂, rfl, u, v', hxe, hu, ht₂⟩), ?_⟩
          rw [catEps_step_inr_some, catEps_mem_εClosure_iff]
          exact Or.inl ⟨t', hstep, rfl⟩

theorem catEps_accepts :
    (catEps M₁ M₂).accepts = concat M₁.accepts M₂.accepts := by
  ext x
  constructor
  · rintro ⟨S, hS, hSeval⟩
    obtain ⟨t, ht, rfl⟩ := hS
    rw [catEps_mem_eval_iff] at hSeval
    rcases hSeval with ⟨s₁, hc, _⟩ | ⟨t', heq, u, v, hx, hu, hv⟩
    · exact absurd hc (by simp)
    · cases heq
      exact ⟨u, hu, v, ⟨t, ht, hv⟩, hx.symm⟩
  · rintro ⟨u, hu, v, hv, rfl⟩
    obtain ⟨t, ht, hteval⟩ := hv
    refine ⟨inr t, ⟨t, ht, rfl⟩, ?_⟩
    rw [catEps_mem_eval_iff]
    exact Or.inr ⟨t, rfl, u, v, rfl, hu, hteval⟩

end

end Exercise722
end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Exercise722
section
set_option linter.unusedVariables false

theorem example_722_cat : ∀ {σ₁ σ₂ : Type} (M₁ : NFA Bool σ₁) (M₂ : NFA Bool σ₂),
  @Eq (Language Bool)
    (@εNFA.accepts Bool (Sum σ₁ σ₂) (@DomainTheory.NeighbourhoodSystems.Exercise722.catEps σ₁ σ₂ M₁ M₂))
    (DomainTheory.NeighbourhoodSystems.Exercise722.concat (@NFA.accepts Bool σ₁ M₁) (@NFA.accepts Bool σ₂ M₂)) :=
  @DomainTheory.NeighbourhoodSystems.Exercise722.catEps_accepts
end

end DomainTheory.NeighbourhoodSystems.Exercise722
namespace DomainTheory.NeighbourhoodSystems
namespace Exercise722
open scoped Computability

section

def sigmaDFA : DFA Bool Unit where
  step _ _ := ()
  start := ()
  accept := Set.univ
end

section
@[simp] theorem sigmaDFA_accepts : sigmaDFA.accepts = Set.univ :=
  Set.eq_univ_of_forall fun _ => Set.mem_univ _
end

section

abbrev SingleState (σ : List Bool) : Type := Option (Fin (σ.length + 1))
end

section

def singleDFA (σ : List Bool) : DFA Bool (SingleState σ) where
  step s b := s.bind fun i =>
    if h : (i : ℕ) < σ.length then
      if σ.get ⟨i, h⟩ = b then some ⟨i + 1, by omega⟩ else none
    else none
  start := some ⟨0, by omega⟩
  accept := {some ⟨σ.length, by omega⟩}
end

section

theorem complDFA_accepts {σ : Type} (M : DFA Bool σ) (a : SExpr) (h : M.accepts = denote a) :
    (Mᶜ).accepts = (denote a)ᶜ := by
  rw [← h]
  ext w
  exact Iff.rfl

example : Fintype (Unit) := inferInstance
example : DecidableEq (Unit) := inferInstance
example (σ : List Bool) : Fintype (SingleState σ) := by unfold SingleState; infer_instance
example (σ : List Bool) : DecidableEq (SingleState σ) := by unfold SingleState; infer_instance
example {σ₁ σ₂ : Type} [Fintype σ₁] [Fintype σ₂] : Fintype (σ₁ × σ₂) := inferInstance
example {σ₁ σ₂ : Type} [DecidableEq σ₁] [DecidableEq σ₂] : DecidableEq (σ₁ × σ₂) := inferInstance
end

section

theorem inter_eval {σ₁ σ₂ : Type} (M₁ : DFA Bool σ₁) (M₂ : DFA Bool σ₂) (w : List Bool) :
    (M₁.inter M₂).eval w = (M₁.eval w, M₂.eval w) := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w a ih =>
    rw [DFA.eval_append_singleton, DFA.eval_append_singleton, DFA.eval_append_singleton, ih]
    rfl
end

section

theorem interDFA_accepts {σ₁ σ₂ : Type} (M₁ : DFA Bool σ₁) (M₂ : DFA Bool σ₂)
    (a b : SExpr) (h₁ : M₁.accepts = denote a) (h₂ : M₂.accepts = denote b) :
    (M₁.inter M₂).accepts = denote (.cap a b) := by
  rw [denote_cap, ← h₁, ← h₂]
  ext w
  constructor
  · intro hw
    have hp : (M₁.inter M₂).eval w ∈ (M₁.inter M₂).accept := hw
    rw [inter_eval] at hp
    exact hp
  · intro hw
    show (M₁.inter M₂).eval w ∈ (M₁.inter M₂).accept
    rw [inter_eval]
    exact hw
end

end Exercise722
end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Exercise722
section
set_option linter.unusedVariables false

theorem example_722_dfa : ∀ {σ₁ σ₂ : Type} (M₁ : DFA Bool σ₁) (M₂ : DFA Bool σ₂) (a b : DomainTheory.NeighbourhoodSystems.Exercise722.SExpr),
  @Eq (Language Bool) (@DFA.accepts Bool σ₁ M₁) (DomainTheory.NeighbourhoodSystems.Exercise722.denote a) →
    @Eq (Language Bool) (@DFA.accepts Bool σ₂ M₂) (DomainTheory.NeighbourhoodSystems.Exercise722.denote b) →
      @Eq (Language Bool) (@DFA.accepts Bool (Prod σ₁ σ₂) (@DFA.inter Bool σ₁ σ₂ M₁ M₂))
        (DomainTheory.NeighbourhoodSystems.Exercise722.denote (a.cap b)) :=
  @DomainTheory.NeighbourhoodSystems.Exercise722.interDFA_accepts
end

end DomainTheory.NeighbourhoodSystems.Exercise722
namespace DomainTheory.NeighbourhoodSystems
namespace Exercise722
open scoped Computability

section
theorem sigmaDFA_accepts_denote : sigmaDFA.accepts = denote .sigma := by
  rw [sigmaDFA_accepts, denote_sigma]
end

section

theorem singleDFA_evalFrom_none (σ : List Bool) (w : List Bool) :
    (singleDFA σ).evalFrom none w = none := by
  induction w with
  | nil => rfl
  | cons b w ih => rw [DFA.evalFrom_cons]; exact ih
end

section

theorem singleDFA_evalFrom (σ : List Bool) (w : List Bool) (k : Fin (σ.length + 1)) :
    (singleDFA σ).evalFrom (some k) w =
      if h : w <+: List.drop (k : ℕ) σ
      then some ⟨(k : ℕ) + w.length, by
        have hlen := h.length_le
        rw [List.length_drop] at hlen
        have := k.isLt
        omega⟩
      else none := by
  induction w generalizing k with
  | nil =>
    rw [DFA.evalFrom_nil, dite_eq_left List.nil_prefix]
    simp
  | cons b w ih =>
    rw [DFA.evalFrom_cons]
    show (singleDFA σ).evalFrom ((singleDFA σ).step (some k) b) w = _
    by_cases hk : (k : ℕ) < σ.length
    · have hdrop : List.drop (k : ℕ) σ = σ.get ⟨k, hk⟩ :: List.drop ((k : ℕ) + 1) σ := by
        rw [List.get_eq_getElem]; exact List.drop_eq_getElem_cons hk
      have hcondiff : ((b :: w) <+: List.drop (k : ℕ) σ) ↔ (b = σ.get ⟨k, hk⟩ ∧ w <+: List.drop ((k : ℕ) + 1) σ) := by
        rw [hdrop, List.cons_prefix_cons]
      by_cases hchar : σ.get ⟨k, hk⟩ = b
      · have hstep : (singleDFA σ).step (some k) b = some ⟨(k : ℕ) + 1, by omega⟩ := by
          simp only [singleDFA, Option.bind_some, dite_eq_left hk, ite_eq_left hchar]
        rw [hstep, ih ⟨(k : ℕ) + 1, by omega⟩]
        by_cases hpre : w <+: List.drop ((k : ℕ) + 1) σ
        · rw [dite_eq_left hpre, dite_eq_left (hcondiff.mpr ⟨hchar.symm, hpre⟩)]
          congr 1
          apply Fin.ext
          simp only [List.length_cons]
          omega
        · rw [dite_eq_right hpre, dite_eq_right (fun hc => hpre (hcondiff.mp hc).2)]
      · have hstep : (singleDFA σ).step (some k) b = none := by
          simp only [singleDFA, Option.bind_some, dite_eq_left hk, ite_eq_right hchar]
        rw [hstep, singleDFA_evalFrom_none, dite_eq_right]
        intro hc
        exact hchar (hcondiff.mp hc).1.symm
    · have hstep : (singleDFA σ).step (some k) b = none := by
        simp only [singleDFA, Option.bind_some, dite_eq_right hk]
      rw [hstep, singleDFA_evalFrom_none, dite_eq_right]
      have hd : List.drop (k : ℕ) σ = [] := by
        rw [List.drop_eq_nil_iff]; have := k.isLt; omega
      rw [hd]; exact (by simp : ¬ (b :: w) <+: [])
end

section

theorem singleDFA_accepts (σ : List Bool) : (singleDFA σ).accepts = {σ} := by
  ext w
  show (singleDFA σ).evalFrom (some ⟨0, by omega⟩) w ∈ (singleDFA σ).accept ↔ _
  rw [singleDFA_evalFrom]
  by_cases h : w <+: List.drop (0 : ℕ) (σ : List Bool)
  · rw [dite_eq_left h, List.drop_zero] at *
    show some (⟨0 + w.length, _⟩ : Fin (σ.length + 1)) ∈ ({some ⟨σ.length, _⟩} : Set _) ↔ w ∈ ({σ} : Set _)
    rw [Set.mem_singleton_iff, Set.mem_singleton_iff, Option.some.injEq, Fin.mk.injEq, Nat.zero_add]
    constructor
    · intro hlen; exact h.eq_of_length hlen
    · intro hw; subst hw; rfl
  · rw [dite_eq_right h, List.drop_zero] at *
    show (none : SingleState σ) ∈ ({some ⟨σ.length, _⟩} : Set _) ↔ w ∈ ({σ} : Set _)
    rw [Set.mem_singleton_iff, Set.mem_singleton_iff]
    constructor
    · intro hcontra; exact absurd hcontra (by simp)
    · intro hw; subst hw; exact absurd List.prefix_rfl h
end

section
theorem singleDFA_accepts_denote (σ : List Bool) : (singleDFA σ).accepts = denote (.single σ) := by
  rw [singleDFA_accepts]; exact (denote_single σ).symm
end

section

def wordsUpTo : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 =>
    (wordsUpTo n) ++ (wordsUpTo n).flatMap fun w => [[false] ++ w, [true] ++ w]
end

section

def anyMatchesB (e : SExpr) (ws : List (List Bool)) : Bool := ws.any (matchesB e)

#eval anyMatchesB .sigma (wordsUpTo 0)
end

section
theorem mem_wordsUpTo (n : ℕ) {w : List Bool} : w ∈ wordsUpTo n ↔ w.length ≤ n := by
  induction n generalizing w with
  | zero =>
    simp only [wordsUpTo, List.mem_singleton]
    constructor
    · rintro (rfl : w = [])
      simp
    · intro h
      exact (List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero h)).symm ▸ rfl
  | succ n ih =>
    simp only [wordsUpTo]
    rw [List.mem_append, List.mem_flatMap]
    constructor
    · intro h
      rcases h with h | ⟨w', hw', hmem⟩
      · exact Nat.le_succ_of_le (ih.mp h)
      · rw [List.mem_cons, List.mem_singleton] at hmem
        rcases hmem with rfl | rfl
        · simpa [List.length_cons] using Nat.succ_le_succ (ih.mp hw')
        · simpa [List.length_cons] using Nat.succ_le_succ (ih.mp hw')
    · intro hlen
      by_cases hw : w.length ≤ n
      · exact Or.inl (ih.mpr hw)
      · match w with
        | [] => exfalso; exact hw (by simp)
        | hd :: tl =>
          have htl_len : tl.length ≤ n := by
            have : tl.length + 1 ≤ n + 1 := by simpa [List.length_cons] using hlen
            exact Nat.le_of_succ_le_succ this
          have htl : tl ∈ wordsUpTo n := ih.mpr htl_len
          refine Or.inr ⟨tl, htl, ?_⟩
          rw [List.mem_cons, List.mem_singleton]
          cases hd with
          | false => exact Or.inl rfl
          | true => exact Or.inr rfl
end

end Exercise722
end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Exercise722
section
set_option linter.unusedVariables false

theorem example_722_words : ∀ (n : Nat) {w : List Bool},
  Iff
    (@Membership.mem (List Bool) (List (List Bool)) (@List.instMembership (List Bool))
      (DomainTheory.NeighbourhoodSystems.Exercise722.wordsUpTo n) w)
    (@LE.le Nat instLENat (@List.length Bool w) n) :=
  DomainTheory.NeighbourhoodSystems.Exercise722.mem_wordsUpTo
end

end DomainTheory.NeighbourhoodSystems.Exercise722
namespace DomainTheory.NeighbourhoodSystems
namespace Exercise722
open scoped Computability
open Sum Set

section
variable {σ₁ σ₂ : Type}
variable {σ : Type}
variable {σ : Type} [Fintype σ] {M : NFA Bool σ}

def pathStateAtAux {s t : σ} {x : List Bool} : M.Path s t x → ∀ n, n ≤ x.length → σ
  | .nil s, 0, _ => s
  | .nil _, n + 1, hn => (Nat.not_succ_le_zero n hn).elim
  | .cons _ s' _ _ _ _ p', 0, _ => s'
  | .cons _ _ _ _ _ _ p', n + 1, hn =>
      pathStateAtAux p' n (Nat.le_of_succ_le_succ hn)

def pathStateAt {s t : σ} {x : List Bool} (p : M.Path s t x) (n : ℕ) (hn : n ≤ x.length) : σ :=
  pathStateAtAux p n hn

structure PathSplit {s t : σ} {x : List Bool} (p : M.Path s t x) (n : ℕ) (hn : n ≤ x.length) where
  u : σ
  hp : M.Path s u (x.take n)
  ht : M.Path u t (x.drop n)
  hu : pathStateAt p n hn = u

end

section
variable {σ₁ σ₂ : Type}

section NFAinterLemmas

def NFAinter (M₁ : NFA Bool σ₁) (M₂ : NFA Bool σ₂) : NFA Bool (σ₁ × σ₂) where
  step s a := {t | t.1 ∈ M₁.step s.1 a ∧ t.2 ∈ M₂.step s.2 a}
  start := {s | s.1 ∈ M₁.start ∧ s.2 ∈ M₂.start}
  accept := {s | s.1 ∈ M₁.accept ∧ s.2 ∈ M₂.accept}

end NFAinterLemmas

section NFAinterLemmas

variable (M₁ : NFA Bool σ₁) (M₂ : NFA Bool σ₂)

theorem NFAinter_mem_eval_iff (x : List Bool) (p : σ₁ × σ₂) :
    p ∈ (NFAinter M₁ M₂).eval x ↔ p.1 ∈ M₁.eval x ∧ p.2 ∈ M₂.eval x := by
  induction x using List.reverseRecOn generalizing p with
  | nil => exact Iff.rfl
  | append_singleton x a ih =>
    rw [NFA.eval_append_singleton, NFA.mem_stepSet]
    constructor
    · rintro ⟨q, hq, hstep⟩
      rw [ih] at hq
      rw [NFA.eval_append_singleton, NFA.mem_stepSet, NFA.eval_append_singleton, NFA.mem_stepSet]
      exact ⟨⟨q.1, hq.1, hstep.1⟩, ⟨q.2, hq.2, hstep.2⟩⟩
    · rintro ⟨h1, h2⟩
      rw [NFA.eval_append_singleton, NFA.mem_stepSet] at h1 h2
      obtain ⟨q1, hq1, hs1⟩ := h1
      obtain ⟨q2, hq2, hs2⟩ := h2
      exact ⟨(q1, q2), (ih (q1, q2)).mpr ⟨hq1, hq2⟩, hs1, hs2⟩

theorem NFAinter_mem_accepts_iff (x : List Bool) :
    x ∈ (NFAinter M₁ M₂).accepts ↔ x ∈ M₁.accepts ∧ x ∈ M₂.accepts := by
  constructor
  · rintro ⟨p, hp, hpe⟩
    rw [NFAinter_mem_eval_iff] at hpe
    exact ⟨⟨p.1, hp.1, hpe.1⟩, ⟨p.2, hp.2, hpe.2⟩⟩
  · rintro ⟨⟨s, hs, hse⟩, ⟨t, ht, hte⟩⟩
    exact ⟨(s, t), ⟨hs, ht⟩, (NFAinter_mem_eval_iff M₁ M₂ x (s, t)).mpr ⟨hse, hte⟩⟩

end NFAinterLemmas

def autState : SExpr → Type
  | .sigma => Unit
  | .single σ => Option (Fin (σ.length + 1))
  | .cap a b => autState a × autState b
  | .cat a b => autState a ⊕ autState b

theorem dfaToNFA_eval {σ : Type} (M : DFA Bool σ) (x : List Bool) :
    M.toNFA.eval x = {M.eval x} := by
  induction x using List.reverseRecOn with
  | nil => rfl
  | append_singleton x a ih =>
    rw [NFA.eval_append_singleton, ih]
    ext s
    rw [NFA.mem_stepSet]
    constructor
    · rintro ⟨t, ht, hs⟩
      rw [Set.mem_singleton_iff] at ht
      subst ht
      rw [Set.mem_singleton_iff, DFA.eval_append_singleton]
      exact hs
    · intro hs
      rw [Set.mem_singleton_iff, DFA.eval_append_singleton] at hs
      exact ⟨M.eval x, Set.mem_singleton _, hs⟩

theorem dfaToNFA_accepts {σ : Type} (M : DFA Bool σ) : M.toNFA.accepts = M.accepts := by
  ext x
  constructor
  · rintro ⟨S, hS, hSe⟩
    rw [dfaToNFA_eval, Set.mem_singleton_iff] at hSe
    rw [DFA.mem_accepts, ← hSe]
    exact hS
  · intro hx
    rw [DFA.mem_accepts] at hx
    exact ⟨M.eval x, hx, by rw [dfaToNFA_eval]; exact Set.mem_singleton _⟩

instance instFintypeAutState : (e : SExpr) → Fintype (autState e)
  | .sigma => inferInstanceAs (Fintype Unit)
  | .single σ => inferInstanceAs (Fintype (Option (Fin (σ.length + 1))))
  | .cap a b => by
      letI := instFintypeAutState a; letI := instFintypeAutState b
      exact inferInstanceAs (Fintype (autState a × autState b))
  | .cat a b => by
      letI := instFintypeAutState a; letI := instFintypeAutState b
      exact inferInstanceAs (Fintype (autState a ⊕ autState b))

instance instDecidableEqAutState : (e : SExpr) → DecidableEq (autState e)
  | .sigma => inferInstanceAs (DecidableEq Unit)
  | .single σ => inferInstanceAs (DecidableEq (Option (Fin (σ.length + 1))))
  | .cap a b => by
      letI := instDecidableEqAutState a; letI := instDecidableEqAutState b
      exact inferInstanceAs (DecidableEq (autState a × autState b))
  | .cat a b => by
      letI := instDecidableEqAutState a; letI := instDecidableEqAutState b
      exact inferInstanceAs (DecidableEq (autState a ⊕ autState b))

def autStateCard : SExpr → ℕ
  | .sigma => 1
  | .single σ => σ.length + 2
  | .cap a b => autStateCard a * autStateCard b
  | .cat a b => autStateCard a + autStateCard b

end

section
variable {σ₁ σ₂ : Type}
variable {σ : Type}

section ShortWord

variable {σ : Type} [Fintype σ] {M : NFA Bool σ}

omit [Fintype σ] in
@[simp] theorem pathStateAt_zero {s t : σ} {x : List Bool} (p : M.Path s t x) :
    pathStateAt p 0 (Nat.zero_le _) = s := by
  cases x with
  | nil =>
    cases p; simp [pathStateAt, pathStateAtAux]
  | cons a xs =>
    cases p with
    | cons _ s' _ _ _ _ _ => simp [pathStateAt, pathStateAtAux]

theorem accepts_card_zero (hσ : Fintype.card σ = 0) {w : List Bool} (hw : w ∈ M.accepts) : False := by
  rw [NFA.mem_accepts] at hw
  obtain ⟨t, ht, hte⟩ := hw
  rw [NFA.mem_evalFrom_iff_exists (S := M.start) (s := t) (x := w)] at hte
  obtain ⟨s, hs, _⟩ := hte
  exact (Fintype.card_eq_zero_iff.mp hσ).elim s

theorem autStateCard_eq_card (e : SExpr) : autStateCard e = Fintype.card (autState e) := by
  induction e with
  | sigma =>
    simp [autStateCard, autState]
    exact (Fintype.card_unique (α := Unit)).symm
  | single σ =>
    simp only [autStateCard, autState]
    have h1 : Fintype.card (Option (Fin (σ.length + 1))) =
        Fintype.card (Fin (σ.length + 1)) + 1 :=
      Fintype.card_option (α := Fin (σ.length + 1))
    have h2 : Fintype.card (Fin (σ.length + 1)) = σ.length + 1 :=
      Fintype.card_fin (σ.length + 1)
    calc autStateCard (.single σ)
        = σ.length + 2 := rfl
      _ = (σ.length + 1) + 1 := rfl
      _ = Fintype.card (Fin (σ.length + 1)) + 1 := (congrArg (fun n => n + 1) h2).symm
      _ = Fintype.card (Option (Fin (σ.length + 1))) := h1.symm
  | cap a b ih_a ih_b =>
    simp [autStateCard, autState, ih_a, ih_b]
    exact (Fintype.card_prod (autState a) (autState b)).symm
  | cat a b ih_a ih_b =>
    simp [autStateCard, autState, ih_a, ih_b]
    exact (Fintype.card_sum (α := autState a) (β := autState b)).symm

end ShortWord

def decideNonemptyB (e : SExpr) : Bool :=
  anyMatchesB e (wordsUpTo (autStateCard e))

def decideEmptyB (e : SExpr) : Bool := !decideNonemptyB e

section ShortWord

variable {σ : Type} [Fintype σ] {M : NFA Bool σ}

omit [Fintype σ] in
theorem mem_accepts_of_path {s t : σ} {x : List Bool} (hs : s ∈ M.start) (ht : t ∈ M.accept)
    (p : M.Path s t x) : x ∈ M.accepts := by
  rw [NFA.accepts_iff_exists_path]
  exact ⟨s, hs, t, ht, ⟨p⟩⟩

def pathAppend {s u t : σ} {a b : List Bool} (p : M.Path s u a) (p' : M.Path u t b) :
    M.Path s t (a ++ b) :=
  match p with
  | .nil _ => p'
  | .cons sMid s' _ a' xs hstep p'' =>
      .cons sMid s' _ a' (xs ++ b) hstep (pathAppend p'' p')

omit [Fintype σ] in
theorem pathStateAt_succ {sMid s' u : σ} {a : Bool} {xs : List Bool}
    (hstep : sMid ∈ M.step s' a) (p' : M.Path sMid u xs) (n : ℕ) (hn : n ≤ xs.length) :
    pathStateAt (.cons sMid s' u a xs hstep p') (n + 1) (Nat.succ_le_succ hn) =
      pathStateAt p' n hn := by
  simp [pathStateAt, pathStateAtAux]

noncomputable def pathAppend_take_drop {s t : σ} {x : List Bool} (p : M.Path s t x) (n : ℕ)
    (hn : n ≤ x.length) : PathSplit p n hn := by
  revert n hn
  induction p with
  | nil s =>
    intro n hn
    have hn0 : n = 0 := Nat.eq_zero_of_le_zero hn
    subst hn0
    exact { u := s, hp := .nil s, ht := .nil s, hu := by rfl }
  | cons sMid s' u a xs hstep p' ih =>
    intro n hn
    cases n with
    | zero =>
      exact { u := s', hp := .nil s', ht := .cons sMid s' u a xs hstep p', hu := by rfl }
    | succ n' =>
      have hn' : n' ≤ xs.length := by simpa [List.length_cons] using hn
      have split := ih n' hn'
      exact {
        u := split.u
        hp := .cons sMid s' split.u a (xs.take n') hstep split.hp
        ht := split.ht
        hu := by rw [pathStateAt_succ hstep p' n' hn']; exact split.hu
      }

omit [Fintype σ] in
theorem accepts_skip_loop {s t : σ} {x : List Bool} {i j : ℕ}
    (hi : i ≤ x.length) (hj : j ≤ x.length) (_hij : i < j)
    (hs : s ∈ M.start) (ht : t ∈ M.accept) (hp : M.Path s t x)
    (heq : pathStateAt hp i hi = pathStateAt hp j hj) :
    x.take i ++ x.drop j ∈ M.accepts := by
  let splitI := pathAppend_take_drop hp i hi
  let splitJ := pathAppend_take_drop hp j hj
  have hqq' : splitI.u = splitJ.u := by rw [← splitI.hu, heq, splitJ.hu]
  exact mem_accepts_of_path hs ht (pathAppend splitI.hp (hqq' ▸ splitJ.ht))

theorem accepts_shorten_step {x : List Bool} (hx : x ∈ M.accepts)
    (hlen : Fintype.card σ ≤ x.length) :
    ∃ y, y ∈ M.accepts ∧ y.length < x.length := by
  rw [NFA.accepts_iff_exists_path] at hx
  obtain ⟨s, hs, t, ht, ⟨hp⟩⟩ := hx
  obtain ⟨i, j, hne, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt
      (f := fun k : Fin (x.length + 1) => pathStateAt hp k.val (Nat.le_of_lt_succ k.isLt))
      (by rw [Fintype.card_fin]; exact Nat.lt_succ_iff.mpr hlen)
  have hval : i.val ≠ j.val := fun h => hne (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hval with hij | hij
  · refine ⟨x.take i.val ++ x.drop j.val, ?_, ?_⟩
    · exact accepts_skip_loop (by omega) (by omega) hij hs ht hp heq
    · have : j.val - i.val > 0 := Nat.sub_pos_of_lt hij
      simp [List.length_append, List.length_take, List.length_drop]
      omega
  · refine ⟨x.take j.val ++ x.drop i.val, ?_, ?_⟩
    · exact accepts_skip_loop (by omega) (by omega) hij hs ht hp heq.symm
    · have : i.val - j.val > 0 := Nat.sub_pos_of_lt hij
      simp [List.length_append, List.length_take, List.length_drop]
      omega

theorem exists_accepted_word_short (h : M.accepts.Nonempty) :
    ∃ w, w.length < Fintype.card σ ∧ w ∈ M.accepts := by
  by_cases hσ : Fintype.card σ = 0
  · obtain ⟨x, hx⟩ := h
    exact (accepts_card_zero hσ hx).elim
  · obtain ⟨x, hx⟩ := h
    exact Nat.strongRecOn x.length
      (motive := fun n =>
        ∀ w, w.length = n → w ∈ M.accepts → ∃ u, u.length < Fintype.card σ ∧ u ∈ M.accepts)
      (fun n ih w hwlen hw => by
        by_cases hlt : n < Fintype.card σ
        · exact ⟨w, hwlen ▸ hlt, hw⟩
        · have hge : Fintype.card σ ≤ n := Nat.not_lt.mp hlt
          obtain ⟨y, hy, hylt⟩ := accepts_shorten_step hw (hwlen.symm ▸ hge)
          exact ih y.length (Nat.lt_of_lt_of_eq hylt hwlen) y rfl hy)
      x rfl hx

end ShortWord

end

section
variable {σ₁ σ₂ : Type}

def toNFA : (e : SExpr) → NFA Bool (autState e)
  | .sigma => sigmaDFA.toNFA
  | .single σ => (singleDFA σ).toNFA
  | .cap a b => NFAinter (toNFA a) (toNFA b)
  | .cat a b => (catEps (toNFA a) (toNFA b)).toNFA

theorem toNFA_accepts : (e : SExpr) → (toNFA e).accepts = denote e
  | .sigma => by
      change sigmaDFA.toNFA.accepts = denote .sigma
      rw [dfaToNFA_accepts sigmaDFA, sigmaDFA_accepts, denote_sigma]
  | .single σ => by
      change (singleDFA σ).toNFA.accepts = denote (.single σ)
      rw [dfaToNFA_accepts (singleDFA σ)]
      exact singleDFA_accepts_denote σ
  | .cap a b => by
      ext x
      change x ∈ (NFAinter (toNFA a) (toNFA b)).accepts ↔ _
      rw [NFAinter_mem_accepts_iff, toNFA_accepts a, toNFA_accepts b, denote_cap]
      exact (Set.mem_inter_iff x (denote a) (denote b)).symm
  | .cat a b => by
      change (catEps (toNFA a) (toNFA b)).toNFA.accepts = denote (.cat a b)
      rw [εNFA.toNFA_correct, catEps_accepts, toNFA_accepts a, toNFA_accepts b, denote_cat]

end

section
variable {σ₁ σ₂ : Type}
variable {σ : Type}

section ShortWord

variable {σ : Type} [Fintype σ] {M : NFA Bool σ}

theorem denote_nonempty_iff_short (e : SExpr) :
    (denote e).Nonempty ↔ ∃ w ∈ wordsUpTo (autStateCard e), matchesB e w = true := by
  have hc : autStateCard e = Fintype.card (autState e) := autStateCard_eq_card e
  constructor
  · intro hne
    rw [← toNFA_accepts e] at hne
    obtain ⟨w, hwlt, hw⟩ := exists_accepted_word_short hne
    refine ⟨w, ?_, ?_⟩
    · rw [mem_wordsUpTo, hc]; omega
    · rw [matchesB_iff, ← toNFA_accepts e]; exact hw
  · intro ⟨w, hwmem, hmatch⟩
    rw [mem_wordsUpTo, hc] at hwmem
    exact ⟨w, (matchesB_iff e w).mp hmatch⟩

end ShortWord

@[simp] theorem decideNonemptyB_iff (e : SExpr) :
    decideNonemptyB e = true ↔ (denote e).Nonempty := by
  simp [decideNonemptyB, anyMatchesB, List.any_eq_true, denote_nonempty_iff_short]

@[simp] theorem decideEmptyB_iff (e : SExpr) :
    decideEmptyB e = true ↔ denote e = ∅ := by
  rw [decideEmptyB, Bool.not_eq_true_eq_eq_false, ← Bool.eq_false_eq_not_eq_true,
    decideNonemptyB_iff, Set.not_nonempty_iff_eq_empty]

instance decidableEmptyDenote (e : SExpr) : Decidable (denote e = ∅) :=
  if h : decideEmptyB e then .isTrue (decideEmptyB_iff e |>.mp h)
  else .isFalse fun he => h (decideEmptyB_iff e |>.mpr he)

#eval decideEmptyB (.cap (.single [false]) (.single [true]))

def consistentB (a b : SExpr) : Bool := !decideEmptyB (.cap a b)

end

section
variable {σ₁ σ₂ : Type}

example : DecidableEq (autState (.sigma : SExpr)) := inferInstance
example : DecidableEq (autState (.single [true, false] : SExpr)) := inferInstance

variable {σ : Type}

@[simp] theorem consistentB_iff (a b : SExpr) :
    consistentB a b = true ↔ (denote (.cap a b)).Nonempty := by
  have h : consistentB a b = decideNonemptyB (.cap a b) := by
    simp [consistentB, decideEmptyB, decideNonemptyB]
  rw [h, decideNonemptyB_iff]

@[simp] theorem capNonempty_iff_consistent (a b : SExpr) :
    (denote a ∩ denote b).Nonempty ↔ consistentB a b = true := by
  rw [← denote_cap, consistentB_iff]
end

section
variable {σ₁ σ₂ : Type}

theorem autStateCard_le_card (e : SExpr) : autStateCard e ≤ Fintype.card (autState e) := by
  induction e with
  | sigma =>
    simp [autStateCard, autState]
    exact (Fintype.card_unique (α := Unit)).ge
  | single σ =>
    have heq : autStateCard (.single σ) = Fintype.card (autState (.single σ)) := by
      simp only [autStateCard, autState]
      have h1 : Fintype.card (Option (Fin (σ.length + 1))) =
          Fintype.card (Fin (σ.length + 1)) + 1 :=
        Fintype.card_option (α := Fin (σ.length + 1))
      have h2 : Fintype.card (Fin (σ.length + 1)) = σ.length + 1 :=
        Fintype.card_fin (σ.length + 1)
      calc σ.length + 2
          = (σ.length + 1) + 1 := rfl
        _ = Fintype.card (Fin (σ.length + 1)) + 1 := (congrArg (fun n => n + 1) h2).symm
        _ = Fintype.card (Option (Fin (σ.length + 1))) := h1.symm
    exact Nat.le_of_eq heq
  | cap a b ih_a ih_b =>
    simp only [autStateCard, autState]
    exact (Nat.mul_le_mul ih_a ih_b).trans (Fintype.card_prod (autState a) (autState b)).ge
  | cat a b ih_a ih_b =>
    simp only [autStateCard, autState]
    exact (Nat.add_le_add ih_a ih_b).trans (Fintype.card_sum (α := autState a) (β := autState b)).ge
end

end Exercise722
end DomainTheory.NeighbourhoodSystems
end

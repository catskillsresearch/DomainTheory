module

public import Mathlib.Order.Directed

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Factoid_1_1
public import Mathlib.Algebra.Group.End
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Order.SetNotation
public import Mathlib.Order.Hom.Basic
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise222
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

section
variable {τ : Type*} (C : Set (Set τ))

/-- The **closure** `F̄ = ⋂ {X ∈ C ∣ F ⊆ X}` of a set `F` relative to the family `C`. -/
def Cl (F : Set τ) : Set τ := ⋂₀ {X | X ∈ C ∧ F ⊆ X}
end

section
variable {τ : Type*} (C : Set (Set τ))
variable (hInter : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → ⋂₀ 𝒮 ∈ C)

include hInter in
/-- Every closure `F̄` of a token lies in `C` (closure under non-empty intersection). -/
theorem Cl_mem {F : Set τ} (h : ∃ X ∈ C, F ⊆ X) : Cl C F ∈ C := by
  show ⋂₀ {X | X ∈ C ∧ F ⊆ X} ∈ C
  apply hInter
  · obtain ⟨X, hX, hFX⟩ := h
    exact ⟨X, hX, hFX⟩
  · intro X hX
    exact hX.1
end

section
variable {τ : Type*} (C : Set (Set τ))

/-- `F̄ ⊆ X` whenever `X ∈ C` contains `F`: the closure is the *smallest* member of `C` over `F`. -/
theorem Cl_subset {F X : Set τ} (hX : X ∈ C) (hFX : F ⊆ X) : Cl C F ⊆ X := by
  intro t ht
  exact (Set.mem_sInter.mp ht) X ⟨hX, hFX⟩

/-- A token: a finite set included in some member of `C`. -/
class IsTok (F : Set τ) : Prop where
  out : F.Finite ∧ ∃ X ∈ C, F ⊆ X

/-- Scott's `Δ`: the type of tokens (finite sets included in members of `C`). -/
abbrev Tok := {F : Set τ // IsTok C F}
end

section
variable {τ : Type*} (C : Set (Set τ))
variable (hInter : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → ⋂₀ 𝒮 ∈ C)

/-- Scott's neighbourhood `C(F) = {G ∈ Δ ∣ F ⊆ Ḡ}`. -/
def nbhd (F : Set τ) : Set (Tok C) := {G | F ⊆ Cl C G.1}

@[simp] theorem mem_nbhd {F : Set τ} {G : Tok C} : G ∈ nbhd C F ↔ F ⊆ Cl C G.1 := Iff.rfl
end

section
variable {τ : Type*} (C : Set (Set τ))
variable (hInter : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → ⋂₀ 𝒮 ∈ C)
variable (hne : C.Nonempty)

include hne in
/-- The empty token `∅ ∈ Δ` (needs `C` non-empty for `∅` to lie in some member). -/
def botTok : Tok C := ⟨∅, ⟨⟨Set.finite_empty, hne.choose, hne.choose_spec, Set.empty_subset _⟩⟩⟩
end

section
variable {τ : Type*} (C : Set (Set τ))
variable (hInter : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → ⋂₀ 𝒮 ∈ C)

/-- `C(∅) = Δ`: the empty token's neighbourhood is everything (the master). -/
theorem nbhd_empty : nbhd C (∅ : Set τ) = Set.univ := by
  ext G
  simp [nbhd]
end

section
variable {τ : Type*} (C : Set (Set τ))

/-- `F ⊆ F̄`: a set is contained in its closure. -/
theorem subset_Cl (F : Set τ) : F ⊆ Cl C F := by
  intro t ht
  rw [Cl, Set.mem_sInter]
  intro X hX
  exact hX.2 ht
end

section
variable {τ : Type*} (C : Set (Set τ))
variable (hInter : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → ⋂₀ 𝒮 ∈ C)

include hInter in
/-- `C(F) ⊆ C(G) ↔ G ⊆ F̄`: comparison of neighbourhoods reduces to inclusion against closures. -/
theorem nbhd_subset_iff {F G : Set τ} (hF : IsTok C F) :
    nbhd C F ⊆ nbhd C G ↔ G ⊆ Cl C F := by
  constructor
  · intro h
    have hmem : (⟨F, hF⟩ : Tok C) ∈ nbhd C F := subset_Cl C F
    exact h hmem
  · intro hG H hH
    exact hG.trans (Cl_subset C (Cl_mem C hInter H.2.out.2) hH)
end

section
variable {τ : Type*} (C : Set (Set τ))
variable (hInter : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → ⋂₀ 𝒮 ∈ C)
variable (hne : C.Nonempty)

include hInter hne in
/-- **The representation neighbourhood system** `reprSystem` over `Δ = Tok C`: neighbourhoods are
exactly the `C(F)` for tokens `F`, the master is all of `Δ = C(∅)`. -/
def reprSystem : NeighborhoodSystem (Tok C) where
  mem N := ∃ F : Tok C, N = nbhd C F.1
  master := Set.univ
  master_nonempty := ⟨botTok C hne, Set.mem_univ _⟩
  master_mem := ⟨botTok C hne, (nbhd_empty C).symm⟩
  inter_mem := by
    rintro X Y Z ⟨F, rfl⟩ ⟨F', rfl⟩ ⟨F'', rfl⟩ hZsub
    have hF''mem : (F'' : Tok C) ∈ nbhd C F''.1 := subset_Cl C F''.1
    have h := hZsub hF''mem
    have hClF'' : Cl C F''.1 ∈ C := Cl_mem C hInter F''.2.out.2
    have hunionsub : F.1 ∪ F'.1 ⊆ Cl C F''.1 := Set.union_subset h.1 h.2
    refine ⟨⟨F.1 ∪ F'.1, ⟨⟨F.2.out.1.union F'.2.out.1, Cl C F''.1, hClF'', hunionsub⟩⟩⟩, ?_⟩
    ext G
    simp only [mem_nbhd, Set.mem_inter_iff, Set.union_subset_iff]
  sub_master := fun _ => Set.subset_univ _

@[simp] theorem mem_reprSystem {N : Set (Tok C)} :
    (reprSystem C hInter hne).mem N ↔ ∃ F : Tok C, N = nbhd C F.1 := Iff.rfl

@[simp] theorem reprSystem_master : (reprSystem C hInter hne).master = Set.univ := rfl

/-- **Directedness step.** If `C(F), C(F') ∈ x` then there is a token `F₃` with `C(F₃) ∈ x` whose
closure dominates both `F̄` and `F̄'`. (From the filter intersection `C(F) ∩ C(F') ∈ x`, which is
some `C(F₃)`.) -/
theorem directed_step (x : (reprSystem C hInter hne).Element) {F F' : Tok C}
    (hF : x.mem (nbhd C F.1)) (hF' : x.mem (nbhd C F'.1)) :
    ∃ F₃ : Tok C, x.mem (nbhd C F₃.1) ∧ Cl C F.1 ⊆ Cl C F₃.1 ∧ Cl C F'.1 ⊆ Cl C F₃.1 := by
  have hinter : x.mem (nbhd C F.1 ∩ nbhd C F'.1) := x.inter_mem hF hF'
  have hmemD : (reprSystem C hInter hne).mem (nbhd C F.1 ∩ nbhd C F'.1) := x.sub hinter
  obtain ⟨F₃, hF₃eq⟩ := hmemD
  rw [hF₃eq] at hinter
  have hF₃self : (F₃ : Tok C) ∈ nbhd C F₃.1 := subset_Cl C F₃.1
  rw [← hF₃eq] at hF₃self
  refine ⟨F₃, hinter, ?_, ?_⟩
  · exact Cl_subset C (Cl_mem C hInter F₃.2.out.2) hF₃self.1
  · exact Cl_subset C (Cl_mem C hInter F₃.2.out.2) hF₃self.2

/-- The family `{F̄ ∣ C(F) ∈ x}` of finite-element closures present in the ideal element `x`. -/
def famC (x : (reprSystem C hInter hne).Element) : Set (Set τ) :=
  {Y | ∃ F : Tok C, x.mem (nbhd C F.1) ∧ Y = Cl C F.1}

/-- The empty token's neighbourhood `C(∅) = Δ` is in every element (it is the master). -/
theorem mem_nbhd_bot (x : (reprSystem C hInter hne).Element) :
    x.mem (nbhd C (botTok C hne).1) := by
  have h : (botTok C hne).1 = (∅ : Set τ) := rfl
  rw [h, nbhd_empty C]
  exact x.master_mem

/-- The ideal element generated by `X ∈ C`: it contains the neighbourhoods above some `C(F)` with
`F ⊆ X`. -/
def ofC (X : Set τ) (hX : X ∈ C) : (reprSystem C hInter hne).Element where
  mem N := (reprSystem C hInter hne).mem N ∧ ∃ F : Tok C, F.1 ⊆ X ∧ nbhd C F.1 ⊆ N
  sub h := h.1
  master_mem :=
    ⟨(reprSystem C hInter hne).master_mem, botTok C hne, Set.empty_subset X, Set.subset_univ _⟩
  inter_mem := by
    rintro N M ⟨hN, F, hFX, hFN⟩ ⟨hM, F', hF'X, hF'M⟩
    have htok : IsTok C (F.1 ∪ F'.1) :=
      ⟨⟨F.2.out.1.union F'.2.out.1, X, hX, Set.union_subset hFX hF'X⟩⟩
    have hsub : nbhd C (F.1 ∪ F'.1) ⊆ N ∩ M := by
      intro G hG
      rw [mem_nbhd, Set.union_subset_iff] at hG
      exact ⟨hFN hG.1, hF'M hG.2⟩
    exact ⟨(reprSystem C hInter hne).inter_mem hN hM ⟨⟨_, htok⟩, rfl⟩ hsub,
      ⟨F.1 ∪ F'.1, htok⟩, Set.union_subset hFX hF'X, hsub⟩
  up_mem := by
    rintro N M ⟨_, F, hFX, hFN⟩ hM hNM
    exact ⟨hM, F, hFX, hFN.trans hNM⟩

/-- Scott's `⋃ {F̄ ∣ C(F) ∈ x}`: the set of `C` represented by the ideal element `x`. -/
def toC (x : (reprSystem C hInter hne).Element) : Set τ := ⋃₀ famC C hInter hne x

theorem mem_toC (x : (reprSystem C hInter hne).Element) {t : τ} :
    t ∈ toC C hInter hne x ↔ ∃ F : Tok C, x.mem (nbhd C F.1) ∧ t ∈ Cl C F.1 := by
  simp only [toC, famC, Set.mem_sUnion, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨Y, ⟨F, hF, rfl⟩, ht⟩
    exact ⟨F, hF, ht⟩
  · rintro ⟨F, hF, ht⟩
    exact ⟨Cl C F.1, ⟨F, hF, rfl⟩, ht⟩

/-- **Finite sets are captured by a single token.** A finite `s ⊆ toC x` is contained in some `F̄`
with `C(F) ∈ x` — the finite-subcover property of the directed union `toC x`. -/
theorem exists_tok_of_finite_subset (x : (reprSystem C hInter hne).Element) {s : Set τ}
    (hs : s.Finite) (hsub : s ⊆ toC C hInter hne x) :
    ∃ F : Tok C, x.mem (nbhd C F.1) ∧ s ⊆ Cl C F.1 := by
  revert hsub
  induction s, hs using Set.Finite.induction_on with
  | empty =>
    intro _
    exact ⟨botTok C hne, mem_nbhd_bot C hInter hne x, Set.empty_subset _⟩
  | @insert a s _ha _hsfin ih =>
    intro hsub
    have ha' : a ∈ toC C hInter hne x := hsub (Set.mem_insert a s)
    rw [mem_toC] at ha'
    obtain ⟨Fa, hFa, haCl⟩ := ha'
    obtain ⟨Fs, hFs, hsCl⟩ := ih (fun y hy => hsub (Set.mem_insert_of_mem a hy))
    obtain ⟨F₃, hF₃, hFaF₃, hFsF₃⟩ := directed_step C hInter hne x hFa hFs
    refine ⟨F₃, hF₃, ?_⟩
    rw [Set.insert_subset_iff]
    exact ⟨hFaF₃ haCl, hsCl.trans hFsF₃⟩

/-- **Key membership identity.** `C(G) ∈ x ↔ G ⊆ toC x`. Forward: `G ⊆ Ḡ ⊆ toC x`. Reverse: `G` is
finite, so the finite-subcover lemma gives `F` with `C(F) ∈ x` and `G ⊆ F̄`, whence `C(F) ⊆ C(G)`
and upward closure gives `C(G) ∈ x`. -/
theorem mem_nbhd_iff (x : (reprSystem C hInter hne).Element) (G : Tok C) :
    x.mem (nbhd C G.1) ↔ G.1 ⊆ toC C hInter hne x := by
  constructor
  · intro hx t ht
    rw [mem_toC]
    exact ⟨G, hx, subset_Cl C G.1 ht⟩
  · intro hsub
    obtain ⟨F, hF, hGF⟩ := exists_tok_of_finite_subset C hInter hne x G.2.out.1 hsub
    have hnsub : nbhd C F.1 ⊆ nbhd C G.1 := (nbhd_subset_iff C hInter F.2).mpr hGF
    exact x.up_mem hF ⟨G, rfl⟩ hnsub
end

section
variable {τ : Type*} (C : Set (Set τ))
variable (hInter : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → ⋂₀ 𝒮 ∈ C)
variable (hne : C.Nonempty)
variable (hDir : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → DirectedOn (· ⊆ ·) 𝒮 → ⋃₀ 𝒮 ∈ C)

include hDir in
/-- `toC x ∈ C`: the represented set lies in the family (closure under directed unions). -/
theorem toC_mem (x : (reprSystem C hInter hne).Element) : toC C hInter hne x ∈ C := by
  show ⋃₀ famC C hInter hne x ∈ C
  apply hDir (famC C hInter hne x)
  · exact ⟨Cl C (botTok C hne).1, botTok C hne, mem_nbhd_bot C hInter hne x, rfl⟩
  · rintro Y ⟨F, _, rfl⟩
    exact Cl_mem C hInter F.2.out.2
  · rintro Y ⟨F, hF, rfl⟩ Y' ⟨F', hF', rfl⟩
    obtain ⟨F₃, hF₃, hFF₃, hF'F₃⟩ := directed_step C hInter hne x hF hF'
    exact ⟨Cl C F₃.1, ⟨F₃, hF₃, rfl⟩, hFF₃, hF'F₃⟩

/-- The other round-trip `ofC (toC x) = x`. -/
theorem ofC_toC (x : (reprSystem C hInter hne).Element) :
    ofC C hInter hne (toC C hInter hne x) (toC_mem C hInter hne hDir x) = x := by
  apply Element.ext
  intro N
  constructor
  · rintro ⟨hN, F, hFtoC, hFN⟩
    have hxF : x.mem (nbhd C F.1) := (mem_nbhd_iff C hInter hne x F).mpr hFtoC
    exact x.up_mem hxF hN hFN
  · intro hxN
    have hN : (reprSystem C hInter hne).mem N := x.sub hxN
    obtain ⟨G, rfl⟩ := hN
    have hGtoC : G.1 ⊆ toC C hInter hne x := (mem_nbhd_iff C hInter hne x G).mp hxN
    exact ⟨⟨G, rfl⟩, G, hGtoC, subset_rfl⟩
end

section
set_option linter.unusedVariables false

theorem example_222.{u_1} : ∀ {τ : Type u_1} (C : Set (Set τ))
  (hInter :
    ∀ (𝒮 : Set (Set τ)),
      @Set.Nonempty (Set τ) 𝒮 →
        @LE.le (Set (Set τ)) (@Set.instLE (Set τ)) 𝒮 C →
          @Membership.mem (Set τ) (Set (Set τ)) (@Set.instMembership (Set τ)) C (@Set.sInter τ 𝒮))
  (hne : @Set.Nonempty (Set τ) C)
  (hDir :
    ∀ (𝒮 : Set (Set τ)),
      @Set.Nonempty (Set τ) 𝒮 →
        @LE.le (Set (Set τ)) (@Set.instLE (Set τ)) 𝒮 C →
          @DirectedOn (Set τ) (fun (x1 x2 : Set τ) => @LE.le (Set τ) (@Set.instLE τ) x1 x2) 𝒮 →
            @Membership.mem (Set τ) (Set (Set τ)) (@Set.instMembership (Set τ)) C (@Set.sUnion τ 𝒮))
  (x :
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
      (@DomainTheory.NeighbourhoodSystems.Exercise222.Tok τ C)
      (@DomainTheory.NeighbourhoodSystems.Exercise222.reprSystem τ C hInter hne)),
  @Eq
    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
      (@DomainTheory.NeighbourhoodSystems.Exercise222.Tok τ C)
      (@DomainTheory.NeighbourhoodSystems.Exercise222.reprSystem τ C hInter hne))
    (@DomainTheory.NeighbourhoodSystems.Exercise222.ofC τ C hInter hne
      (@DomainTheory.NeighbourhoodSystems.Exercise222.toC τ C hInter hne x)
      (@DomainTheory.NeighbourhoodSystems.Exercise222.toC_mem τ C hInter hne hDir x))
    x :=
  @DomainTheory.NeighbourhoodSystems.Exercise222.ofC_toC
end

section
variable {τ : Type*} (C : Set (Set τ))
variable (hInter : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → ⋂₀ 𝒮 ∈ C)
variable (hne : C.Nonempty)

/-- **Scott's identity** `X = ⋃ {F̄ ∣ F ⊆ X, F ∈ Δ}` in round-trip form: `toC (ofC X) = X`. -/
theorem toC_ofC (X : Set τ) (hX : X ∈ C) : toC C hInter hne (ofC C hInter hne X hX) = X := by
  apply Set.Subset.antisymm
  · intro t ht
    rw [mem_toC] at ht
    obtain ⟨F, hF, htCl⟩ := ht
    obtain ⟨_, F', hF'X, hF'F⟩ := hF
    have h1 : F.1 ⊆ Cl C F'.1 := (nbhd_subset_iff C hInter F'.2).mp hF'F
    have hFX : F.1 ⊆ X := h1.trans (Cl_subset C hX hF'X)
    exact Cl_subset C hX hFX htCl
  · intro t ht
    have hst : IsTok C {t} := ⟨⟨Set.finite_singleton t, X, hX, Set.singleton_subset_iff.mpr ht⟩⟩
    rw [mem_toC]
    refine ⟨⟨{t}, hst⟩, ?_, subset_Cl C {t} rfl⟩
    exact ⟨⟨⟨{t}, hst⟩, rfl⟩, ⟨{t}, hst⟩, Set.singleton_subset_iff.mpr ht, subset_rfl⟩
end

section
variable {τ : Type*} (C : Set (Set τ))
variable (hInter : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → ⋂₀ 𝒮 ∈ C)
variable (hne : C.Nonempty)
variable (hDir : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → DirectedOn (· ⊆ ·) 𝒮 → ⋃₀ 𝒮 ∈ C)

include hDir in
/- concordance: source L922 EXERCISE 2.22 domains from closure properties -/
/-- **Exercise 2.22 — the representation theorem.** `C`, ordered by inclusion, is order-isomorphic
to the domain `|reprSystem|`. The isomorphism sends `x ↦ ⋃ {F̄ ∣ C(F) ∈ x}` (`toC`) and
`X ↦ {C(F) ∣ F ⊆ X}` (`ofC`). -/
def reprIso : (reprSystem C hInter hne).Element ≃o {X : Set τ // X ∈ C} where
  toFun x := ⟨toC C hInter hne x, toC_mem C hInter hne hDir x⟩
  invFun X := ofC C hInter hne X.1 X.2
  left_inv x := ofC_toC C hInter hne hDir x
  right_inv X := Subtype.ext (toC_ofC C hInter hne X.1 X.2)
  map_rel_iff' := by
    intro a b
    show toC C hInter hne a ⊆ toC C hInter hne b ↔ a ≤ b
    constructor
    · intro hsub N hN
      have hmemD : (reprSystem C hInter hne).mem N := a.sub hN
      obtain ⟨G, rfl⟩ := hmemD
      have hGa : G.1 ⊆ toC C hInter hne a := (mem_nbhd_iff C hInter hne a G).mp hN
      exact (mem_nbhd_iff C hInter hne b G).mpr (hGa.trans hsub)
    · intro hab t ht
      rw [mem_toC] at ht ⊢
      obtain ⟨F, hF, htCl⟩ := ht
      exact ⟨F, hab _ hF, htCl⟩
end

end DomainTheory.NeighbourhoodSystems.Exercise222

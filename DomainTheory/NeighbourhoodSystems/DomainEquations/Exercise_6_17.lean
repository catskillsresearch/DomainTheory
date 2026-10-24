module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise_4_19
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise_5_16
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_12
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Theorem_2_7
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem_6_16

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition_6_6
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Factoid_1_8
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

open Example62C in
/- concordance: source L4077 EXERCISE 6.17 algebras for sequence domains -/
/-- **Exercise 6.17 — the functor `T(X) = 𝟙 + X + X`** on the category of `∅`-free domains and strict
maps. On objects, `T(D) = 𝟙 + D + D` (Example 6.2's three-way sum); on maps, `T(f) = I_𝟙 + f + f`. -/
abbrev Tc : Endofunctor StrictDomainObj.{w} where
  obj := tcObj
  map := tcMapHom
  map_id D := Subtype.ext (by
    show sumMap3 (idMap unitSys) (idMap D.sys) (idMap D.sys) = idMap (tcObj D).sys
    exact sumMap3_id)
  map_comp {D E F} g f := Subtype.ext (by
    show sumMap3 (idMap unitSys) (g.1.comp f.1) (g.1.comp f.1)
      = (sumMap3 (idMap unitSys) g.1 g.1).comp (sumMap3 (idMap unitSys) f.1 f.1)
    have h := sumMap3_comp (h₀ := Example62C.unitSys_nonempty) (h₁ := D.nonempty) (h₂ := D.nonempty)
      (h₀' := Example62C.unitSys_nonempty) (h₁' := E.nonempty) (h₂' := E.nonempty)
      (h₀'' := Example62C.unitSys_nonempty) (h₁'' := F.nonempty) (h₂'' := F.nonempty)
      (idMap unitSys) g.1 g.1 (idMap unitSys) f.1 f.1
    rw [idMap_comp] at h
    exact h)

@[simp] theorem Tc_obj (D : StrictDomainObj.{w}) : Tc.obj D = tcObj D := rfl

@[simp] theorem Tc_map_val {D E : StrictDomainObj.{w}} (f : (D ⟶ E)) :
    (Tc.map f).1 = sumMap3 (h₀ := Example62C.unitSys_nonempty) (h₁ := D.nonempty) (h₂ := D.nonempty)
      (h₀' := Example62C.unitSys_nonempty) (h₁' := E.nonempty) (h₂' := E.nonempty)
      (idMap unitSys) f.1 f.1 := rfl

open Example44 Example62C ExampleB in
/-- `C` (Example 4.4: finite-or-infinite binary sequences) as an object of the `∅`-free category. -/
abbrev Cobj : StrictDomainObj.{0} := ⟨Str, C, C_nonempty⟩

end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

namespace Example62C

open Example44 ExampleB Example62

@[simp] theorem ccEquiv_apply (x : C.Element) : ccEquiv x = toCC x := rfl

/-- `(b·z).mem (bX) ↔ z.mem X`: the `b`-successor's filter restricted to the `b`-copy is `z`. -/
theorem consMap_mem_embBit {b : Bool} {z : C.Element} {X : Set Str} (hX : C.mem X) :
    ((consMap b).toElementMap z).mem (embBit b X) ↔ z.mem X := by
  constructor
  · rintro ⟨X', hzX', _, _, hsub⟩
    rw [← embBit_eq_prepend] at hsub
    exact z.up_mem hzX' hX (embBit_subset.mp hsub)
  · intro hz
    refine ⟨X, hz, z.sub hz, memC_embBit b hX, ?_⟩
    rw [← embBit_eq_prepend]

/-- `(b·z)` never meets the `(¬b)`-copy: `0z` avoids the `1`-copies and vice versa (used to discharge
the cross-tag cases in `toCC_consMap`). -/
theorem consMap_not_mem_embBit_ne {b c : Bool} (hbc : b ≠ c) {z : C.Element} {X : Set Str} :
    ¬ ((consMap b).toElementMap z).mem (embBit c X) := by
  rintro ⟨X', hzX', hX'mem, _, hsub⟩
  obtain ⟨a, ha⟩ := C_nonempty X' hX'mem
  rw [← embBit_eq_prepend] at hsub
  obtain ⟨w, hw, heq⟩ := hsub ⟨a, rfl, ha⟩
  rw [List.cons.injEq] at hw; exact hbc hw.1

/-- `(b·z)` avoids the terminator `{Λ}` (since `bσ ≠ Λ`). -/
theorem consMap_not_mem_nil {b : Bool} {z : C.Element} :
    ¬ ((consMap b).toElementMap z).mem ({[]} : Set Str) := by
  rintro ⟨X', hzX', hX'mem, _, hsub⟩
  obtain ⟨a, ha⟩ := C_nonempty X' hX'mem
  rw [← embBit_eq_prepend] at hsub
  have := hsub ⟨a, rfl, ha⟩
  rw [Set.mem_singleton_iff] at this; exact absurd this (by simp)

end Example62C
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

section Initial

open Example44 Example62C ExampleB Exercise419 Exercise516

variable (B : TAlgebra Tc)

/-- The distinguished point `e = k(Λ)`: the image under `k` of the terminator (`𝟙`-injection). -/
def descE : B.carrier.sys.Element :=
  B.str.1.toElementMap (sinj0 (h₀ := Example62C.unitSys_nonempty) (h₁ := B.carrier.nonempty)
    (h₂ := B.carrier.nonempty) unitSys.bot)

/-- The `b`-th successor operation `f_b = k ∘ inj_b`: `f₀` via the `0`-copy (`inj₁`), `f₁` via the
`1`-copy (`inj₂`). -/
def descF (b : Bool) (y : B.carrier.sys.Element) : B.carrier.sys.Element :=
  B.str.1.toElementMap (cond b
    (sinj2 (h₀ := Example62C.unitSys_nonempty) (h₁ := B.carrier.nonempty) (h₂ := B.carrier.nonempty) y)
    (sinj1 (h₀ := Example62C.unitSys_nonempty) (h₁ := B.carrier.nonempty) (h₂ := B.carrier.nonempty) y))

theorem descF_mono (b : Bool) {y y' : B.carrier.sys.Element} (h : y ≤ y') :
    descF B b y ≤ descF B b y' := by
  cases b
  · exact B.str.1.toElementMap_mono (sinj1_mono h)
  · exact B.str.1.toElementMap_mono (sinj2_mono h)

/-- The recursion `φ(Λ)=z`, `φ(b·σ)=f_b(φ(σ))` on a finite string, with base value `z`. -/
def descVal (z : B.carrier.sys.Element) : Str → B.carrier.sys.Element
  | [] => z
  | b :: σ => descF B b (descVal z σ)

theorem descVal_append (z : B.carrier.sys.Element) (σ ρ : Str) :
    descVal B z (σ ++ ρ) = descVal B (descVal B z ρ) σ := by
  induction σ with
  | nil => rfl
  | cons b σ ih => exact congrArg (descF B b) ih

theorem descVal_mono_z {z z' : B.carrier.sys.Element} (h : z ≤ z') :
    ∀ σ, descVal B z σ ≤ descVal B z' σ
  | [] => h
  | _ :: σ => descF_mono B _ (descVal_mono_z h σ)

theorem descMap_hcone {σ τ : Str} (h : σ <+: τ) :
    descVal B B.carrier.sys.bot σ ≤ descVal B B.carrier.sys.bot τ := by
  obtain ⟨ρ, rfl⟩ := h
  rw [descVal_append]
  exact descVal_mono_z B (B.carrier.sys.bot_le _) σ

theorem descMap_hsing {σ τ : Str} (h : σ <+: τ) :
    descVal B B.carrier.sys.bot σ ≤ descVal B (descE B) τ := by
  obtain ⟨ρ, rfl⟩ := h
  rw [descVal_append]
  exact descVal_mono_z B (B.carrier.sys.bot_le _) σ

end Initial

end

end DomainTheory.NeighbourhoodSystems
end

section
/- concordance: source L4075 EXERCISES — Lecture VI exercises -/
-- Exercise617/descMap.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

section Initial

open Example44 Example62C ExampleB Exercise419 Exercise516

variable (B : TAlgebra Tc)

/-- **The homomorphism `C → E`.** Built by `liftC` from the head-recursion: `φ(σ⊥) = f_{σ}(⊥)` and
`φ(σ) = f_{σ}(e)`, interpreting `b₀b₁… ↦ f_{b₀}(f_{b₁}(…))`. -/
def descMap : ApproximableMap C B.carrier.sys :=
  liftC B.carrier.sys (descVal B B.carrier.sys.bot) (descVal B (descE B))
    (fun {_ _} => descMap_hcone B) (fun {_ _} => descMap_hsing B)

end Initial

end DomainTheory.NeighbourhoodSystems
end

section
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

section
section Initial

open Example44 Example62C ExampleB Exercise419 Exercise516

variable (B : TAlgebra Tc)

@[simp] theorem descMap_strBot (σ : Str) :
    (descMap B).toElementMap (strBot σ) = descVal B B.carrier.sys.bot σ :=
  liftC_strBot _ _ _ _ _ σ

end Initial
end

section
section Initial

open Example44 Example62C ExampleB Exercise419 Exercise516

variable (B : TAlgebra Tc)

@[simp] theorem descMap_strElem (σ : Str) :
    (descMap B).toElementMap (strElem σ) = descVal B (descE B) σ :=
  liftC_strElem _ _ _ _ _ σ

end Initial
end

section
section Initial

open Example44 Example62C ExampleB Exercise419 Exercise516

variable (B : TAlgebra Tc)

theorem C_bot_eq_strBot_nil : C.bot = strBot [] := by
  apply NeighborhoodSystem.Element.ext
  intro Y
  show (C.mem Y ∧ C.master ⊆ Y) ↔ (C.mem Y ∧ cone [] ⊆ Y)
  rw [C_master, cone_nil]

end Initial
end

section
section Initial

open Example44 Example62C ExampleB Exercise419 Exercise516

variable (B : TAlgebra Tc)

theorem ccEquiv_comp_symm :
    (ofIso ccEquiv).comp (ofIso ccEquiv.symm) = idMap (sum3 unitSys C C Example62C.unitSys_nonempty
      Example62C.C_nonempty Example62C.C_nonempty) := by
  apply ext_of_toElementMap
  intro s
  rw [toElementMap_comp, toElementMap_ofIso, toElementMap_ofIso, toElementMap_idMap]
  exact ccEquiv.apply_symm_apply s

end Initial
end

section
section Initial

open Example44 Example62C ExampleB Exercise419 Exercise516

variable (B : TAlgebra Tc)

theorem ccEquiv_symm_comp : (ofIso ccEquiv.symm).comp (ofIso ccEquiv) = idMap C := by
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_comp, toElementMap_ofIso, toElementMap_ofIso, toElementMap_idMap]
  exact ccEquiv.symm_apply_apply x

end Initial
end

section
section Initial

open Example44 Example62C ExampleB Exercise419 Exercise516

variable (B : TAlgebra Tc)

theorem descMap_strict : IsStrict (descMap B) := by
  rw [isStrict_iff_apply_bot, C_bot_eq_strBot_nil, descMap_strBot]
  rfl

end Initial
end

section
section Initial

open Example44 Example62C ExampleB Exercise419 Exercise516

variable (B : TAlgebra Tc)

/-- The bundled strict homomorphism `C → E`. -/
def descStrict : (Cobj ⟶ B.carrier) := ⟨descMap B, descMap_strict B⟩

end Initial
end

section
section Initial

open Example44 Example62C ExampleB Exercise419 Exercise516

variable (B : TAlgebra Tc)

/-- `T(g)` on `⊥` is `⊥`; precomposed with `k` it is `⊥` (both maps are strict). -/
theorem genKeyBot (g : ApproximableMap C B.carrier.sys) :
    B.str.1.toElementMap ((sumMap3 (h₀ := Example62C.unitSys_nonempty) (h₁ := Example62C.C_nonempty)
        (h₂ := Example62C.C_nonempty) (h₀' := Example62C.unitSys_nonempty) (h₁' := B.carrier.nonempty)
        (h₂' := B.carrier.nonempty) (idMap unitSys) g g).toElementMap (toCC (strBot [])))
      = B.carrier.sys.bot := by
  have hb : toCC (strBot []) = (sum3 unitSys C C Example62C.unitSys_nonempty Example62C.C_nonempty
      Example62C.C_nonempty).bot := by
    rw [← C_bot_eq_strBot_nil, ← Example62C.ccEquiv_apply]; exact ccEquiv.map_bot
  rw [hb, isStrict_iff_apply_bot.mp (isStrict_sumMap3 (h₀ := Example62C.unitSys_nonempty)
    (h₁ := Example62C.C_nonempty) (h₂ := Example62C.C_nonempty) (idMap unitSys) g g)]
  exact isStrict_iff_apply_bot.mp B.str.2

end Initial
end

section
/-- The map of an order-isomorphism is strict (an iso of domains preserves `⊥`). -/
theorem isStrict_ofIso {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
    (e : V₀.Element ≃o V₁.Element) : IsStrict (ofIso e) := by
  rw [isStrict_iff_apply_bot, toElementMap_ofIso]
  exact e.map_bot
end

section
open Example44 Example62C in
/-- **The `T`-algebra structure on `C`.** `(tcObj Cobj).sys = 𝟙 + C + C` (definitionally Example 6.2's
`CC`), and the structure map `i : 𝟙 + C + C → C` is the inverse of the domain-equation isomorphism
`ccEquiv` (Example 6.2), realised as an approximable map by `ofIso`; it is strict by `isStrict_ofIso`.
Concretely `i` sends the terminator to `Λ̂` and each `b`-copy of `x` to `b·x`. -/
abbrev cStr : ((Tc.obj Cobj) ⟶ Cobj) :=
  ⟨ofIso (by exact ccEquiv.symm), isStrict_ofIso _⟩
end

section
open Example44 Example62C in
/-- **`C` is a `T`-algebra**, `(C, i)` with `T(X) = 𝟙 + X + X`. -/
abbrev Calg : TAlgebra Tc := ⟨Cobj, cStr⟩
end

section
namespace Example62C

open Example44 ExampleB Example62

/-- **`toCC ∘ (0·) = inj₁` and `toCC ∘ (1·) = inj₂`.** Prepending the bit `b` to `z` is, across the
isomorphism `C ≅ 𝟙+C+C`, the injection of `z` into the `b`-th `C`-summand. -/
theorem toCC_consMap (b : Bool) (z : C.Element) :
    toCC ((consMap b).toElementMap z)
      = cond b
          (sinj2 (V₀ := unitSys) (V₁ := C) (h₀ := unitSys_nonempty) (h₁ := C_nonempty)
            (h₂ := C_nonempty) z)
          (sinj1 (V₀ := unitSys) (V₂ := C) (h₀ := unitSys_nonempty) (h₁ := C_nonempty)
            (h₂ := C_nonempty) z) := by
  apply NeighborhoodSystem.Element.ext
  intro W
  cases b
  · simp only [Bool.cond_false]
    constructor
    · rintro (rfl | ⟨rfl, hz⟩ | ⟨X, hX, rfl, hz⟩ | ⟨Y, hY, rfl, hz⟩)
      · exact Or.inl rfl
      · exact absurd hz consMap_not_mem_nil
      · exact Or.inr ⟨X, hX, rfl, (consMap_mem_embBit hX).mp hz⟩
      · exact absurd hz (consMap_not_mem_embBit_ne (by decide))
    · rintro (rfl | ⟨Y, hY, rfl, hz⟩)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inl ⟨Y, hY, rfl, (consMap_mem_embBit hY).mpr hz⟩))
  · simp only [Bool.cond_true]
    constructor
    · rintro (rfl | ⟨rfl, hz⟩ | ⟨X, hX, rfl, hz⟩ | ⟨Y, hY, rfl, hz⟩)
      · exact Or.inl rfl
      · exact absurd hz consMap_not_mem_nil
      · exact absurd hz (consMap_not_mem_embBit_ne (by decide))
      · exact Or.inr ⟨Y, hY, rfl, (consMap_mem_embBit hY).mp hz⟩
    · rintro (rfl | ⟨Y, hY, rfl, hz⟩)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inr ⟨Y, hY, rfl, (consMap_mem_embBit hY).mpr hz⟩))

end Example62C
end

section
section Initial

open Example44 Example62C ExampleB Exercise419 Exercise516

variable (B : TAlgebra Tc)

/-- The composite `inj₀∘(...)` of `T(g)` applied to a successor reduces to the operation `f_b`. The
single computational step behind both existence and uniqueness, for an *arbitrary* `g`. -/
theorem genKey (g : ApproximableMap C B.carrier.sys) (b : Bool) (w : C.Element) :
    B.str.1.toElementMap ((sumMap3 (h₀ := Example62C.unitSys_nonempty) (h₁ := Example62C.C_nonempty)
        (h₂ := Example62C.C_nonempty) (h₀' := Example62C.unitSys_nonempty) (h₁' := B.carrier.nonempty)
        (h₂' := B.carrier.nonempty) (idMap unitSys) g g).toElementMap
      (toCC ((consMap b).toElementMap w)))
      = descF B b (g.toElementMap w) := by
  rw [toCC_consMap]
  cases b
  · simp only [Bool.cond_false]; rw [sumMap3_sinj1]; rfl
  · simp only [Bool.cond_true]; rw [sumMap3_sinj2]; rfl

end Initial
end

section
namespace Example62C

open Example44 ExampleB Example62

/-- **`toCC Λ̂ = inj₀`.** The finished empty sequence is the terminator (the `𝟙`-summand). -/
theorem toCC_strElem_nil :
    toCC (strElem []) = sinj0 (V₁ := C) (V₂ := C) (h₀ := unitSys_nonempty) (h₁ := C_nonempty)
      (h₂ := C_nonempty) unitSys.bot := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨rfl, hz⟩ | ⟨X, hX, rfl, hz⟩ | ⟨Y, hY, rfl, hz⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨Set.univ, rfl, rfl, unitSys.bot.master_mem⟩
    · exact absurd (hz.2 (Set.mem_singleton_iff.mpr rfl)) nil_not_mem_embBit
    · exact absurd (hz.2 (Set.mem_singleton_iff.mpr rfl)) nil_not_mem_embBit
  · rintro (rfl | ⟨X, hX, rfl, hz⟩)
    · exact Or.inl rfl
    · obtain rfl : X = Set.univ := hX
      exact Or.inr (Or.inl ⟨rfl, memC_singleton [], subset_rfl⟩)

end Example62C
end

section
section Initial

open Example44 Example62C ExampleB Exercise419 Exercise516

variable (B : TAlgebra Tc)

/-- `T(g)` on the terminator is the terminator; precomposed with `k` it is `e`. -/
theorem genKey0 (g : ApproximableMap C B.carrier.sys) :
    B.str.1.toElementMap ((sumMap3 (h₀ := Example62C.unitSys_nonempty) (h₁ := Example62C.C_nonempty)
        (h₂ := Example62C.C_nonempty) (h₀' := Example62C.unitSys_nonempty) (h₁' := B.carrier.nonempty)
        (h₂' := B.carrier.nonempty) (idMap unitSys) g g).toElementMap (toCC (strElem [])))
      = descE B := by
  rw [toCC_strElem_nil, sumMap3_sinj0, toElementMap_idMap]
  rfl

end Initial
end

section
section Initial

open Example44 Example62C ExampleB Exercise419 Exercise516

variable (B : TAlgebra Tc)

/-- `C`'s algebra map satisfies the recursion. -/
theorem descMap_satisfiesRec :
    descMap B = (B.str.1.comp (sumMap3 (h₀ := Example62C.unitSys_nonempty)
        (h₁ := Example62C.C_nonempty) (h₂ := Example62C.C_nonempty) (h₀' := Example62C.unitSys_nonempty)
        (h₁' := B.carrier.nonempty) (h₂' := B.carrier.nonempty) (idMap unitSys) (descMap B)
        (descMap B))).comp (ofIso ccEquiv) := by
  apply map_ext_C
  · intro σ
    rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, descMap_strBot]
    cases σ with
    | nil => exact (genKeyBot B (descMap B)).symm
    | cons b σ =>
      rw [Example62C.ccEquiv_apply, ← consMap_strBot]
      have h := genKey B (descMap B) b (strBot σ)
      rw [descMap_strBot] at h
      exact h.symm
  · intro σ
    rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, descMap_strElem]
    cases σ with
    | nil => exact (genKey0 B (descMap B)).symm
    | cons b σ =>
      rw [Example62C.ccEquiv_apply, ← consMap_strElem]
      have h := genKey B (descMap B) b (strElem σ)
      rw [descMap_strElem] at h
      exact h.symm

end Initial
end

section
section Initial

open Example44 Example62C ExampleB Exercise419 Exercise516

variable (B : TAlgebra Tc)

/-- **The homomorphism square**, read off at the level of underlying approximable maps:
`desc ∘ i = k ∘ T(desc)`. -/
theorem descComm : (descMap B).comp (ofIso ccEquiv.symm)
    = B.str.1.comp (sumMap3 (h₀ := Example62C.unitSys_nonempty) (h₁ := Example62C.C_nonempty)
        (h₂ := Example62C.C_nonempty) (h₀' := Example62C.unitSys_nonempty) (h₁' := B.carrier.nonempty)
        (h₂' := B.carrier.nonempty) (idMap unitSys) (descMap B) (descMap B)) := by
  conv_lhs => rw [descMap_satisfiesRec B]
  rw [comp_assoc, ccEquiv_comp_symm, comp_idMap]

end Initial
end

section
section Initial

open Example44 Example62C ExampleB Exercise419 Exercise516

variable (B : TAlgebra Tc)

/-- **The descent homomorphism `(C, i) → (E, k)`** as a `T`-algebra homomorphism. -/
def descAlgHom : AlgHom Calg B where
  hom := descStrict B
  comm := by
    apply Subtype.ext
    simp only [StrictDomainObj.comp_val]
    exact descComm B

end Initial
end

section
section Initial

open Example44 Example62C ExampleB Exercise419 Exercise516

variable (B : TAlgebra Tc)

/-- **Any map satisfying the homomorphism recursion equals `descMap`.** This is *both* the existence
witness (`descMap` satisfies it) and the uniqueness driver. -/
theorem rec_determines (g : ApproximableMap C B.carrier.sys)
    (hg : g = (B.str.1.comp (sumMap3 (h₀ := Example62C.unitSys_nonempty) (h₁ := Example62C.C_nonempty)
        (h₂ := Example62C.C_nonempty) (h₀' := Example62C.unitSys_nonempty) (h₁' := B.carrier.nonempty)
        (h₂' := B.carrier.nonempty) (idMap unitSys) g g)).comp (ofIso ccEquiv)) :
    g = descMap B := by
  have hbot : ∀ σ, g.toElementMap (strBot σ) = descVal B B.carrier.sys.bot σ := by
    intro σ
    induction σ with
    | nil =>
      conv_lhs => rw [hg]
      rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, Example62C.ccEquiv_apply]
      exact genKeyBot B g
    | cons b σ ih =>
      conv_lhs => rw [hg]
      rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, Example62C.ccEquiv_apply,
        ← consMap_strBot]
      have h := genKey B g b (strBot σ)
      rw [ih] at h
      exact h
  have helem : ∀ σ, g.toElementMap (strElem σ) = descVal B (descE B) σ := by
    intro σ
    induction σ with
    | nil =>
      conv_lhs => rw [hg]
      rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, Example62C.ccEquiv_apply]
      exact genKey0 B g
    | cons b σ ih =>
      conv_lhs => rw [hg]
      rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, Example62C.ccEquiv_apply,
        ← consMap_strElem]
      have h := genKey B g b (strElem σ)
      rw [ih] at h
      exact h
  apply map_ext_C
  · intro σ; rw [hbot, descMap_strBot]
  · intro σ; rw [helem, descMap_strElem]

end Initial
end

section
section Initial

open Example44 Example62C ExampleB Exercise419 Exercise516

variable (B : TAlgebra Tc)

/-- **Uniqueness.** Any `T`-algebra homomorphism out of `(C, i)` equals `descAlgHom`. -/
theorem descAlgHom_uniq (h' : AlgHom Calg B) : h' = descAlgHom B := by
  obtain ⟨hom, comm⟩ := h'
  have hg : hom.1 = descMap B := by
    refine rec_determines B hom.1 ?_
    have hc : hom.1.comp (ofIso ccEquiv.symm)
        = B.str.1.comp (sumMap3 (h₀ := Example62C.unitSys_nonempty) (h₁ := Example62C.C_nonempty)
          (h₂ := Example62C.C_nonempty) (h₀' := Example62C.unitSys_nonempty) (h₁' := B.carrier.nonempty)
          (h₂' := B.carrier.nonempty) (idMap unitSys) hom.1 hom.1) :=
      congrArg Subtype.val comm
    have h2 := congrArg (fun m => m.comp (ofIso ccEquiv)) hc
    simp only at h2
    rw [comp_assoc] at h2
    erw [ccEquiv_symm_comp, comp_idMap] at h2
    exact h2
  have hhom : hom = descStrict B := Subtype.ext hg
  subst hhom
  rfl

end Initial
end

section
/-- **Exercise 6.17 (existence half) — `(C, i)` is an initial `T`-algebra for `T(X) = 𝟙 + X + X`.**
The descent map `φ : C → E` is the closed-form head-recursion `φ(Λ) = e`, `φ(b·x) = f_b(φ x)`
(`f_b = k ∘ inj_b`), built choice-free via `liftC`; it is the unique `T`-algebra homomorphism, so `C`
is determined (up to iso, Proposition 6.6) as the initial algebra of `X ↦ 𝟙 + X + X`. -/
def CisInitial : IsInitial Calg where
  desc := descAlgHom
  uniq := fun B h => descAlgHom_uniq B h
end

section
set_option linter.unusedVariables false

theorem example_617 : ∀
  (B :
    @DomainTheory.NeighbourhoodSystems.TAlgebra DomainTheory.NeighbourhoodSystems.StrictDomainObj
      DomainTheory.NeighbourhoodSystems.instCategoryStrictDomainObj DomainTheory.NeighbourhoodSystems.Tc)
  (h' :
    @DomainTheory.NeighbourhoodSystems.AlgHom DomainTheory.NeighbourhoodSystems.StrictDomainObj
      DomainTheory.NeighbourhoodSystems.instCategoryStrictDomainObj DomainTheory.NeighbourhoodSystems.Tc
      DomainTheory.NeighbourhoodSystems.Calg B),
  @Eq
    (@DomainTheory.NeighbourhoodSystems.AlgHom DomainTheory.NeighbourhoodSystems.StrictDomainObj
      DomainTheory.NeighbourhoodSystems.instCategoryStrictDomainObj DomainTheory.NeighbourhoodSystems.Tc
      DomainTheory.NeighbourhoodSystems.Calg B)
    h' (DomainTheory.NeighbourhoodSystems.descAlgHom B) :=
  DomainTheory.NeighbourhoodSystems.descAlgHom_uniq
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Exercise617Gen
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

section
variable {A : Type} [DecidableEq A]

/-- The token type `A*` of finite `A`-strings. -/
abbrev Strn (A : Type) := List A

/-- The cone `σA*`: all extensions of `σ`. -/
def coneN (σ : Strn A) : Set (Strn A) := {w | σ <+: w}

omit [DecidableEq A] in

@[simp] theorem mem_coneN {σ w : Strn A} : w ∈ coneN σ ↔ σ <+: w := Iff.rfl

omit [DecidableEq A] in

theorem coneN_nil : coneN ([] : Strn A) = Set.univ := by ext w; simp [coneN]

omit [DecidableEq A] in

theorem coneN_subset_coneN {σ τ : Strn A} : coneN σ ⊆ coneN τ ↔ τ <+: σ := by
  constructor
  · intro h; exact h (show σ ∈ coneN σ from List.prefix_rfl)
  · intro hτσ w hw; exact hτσ.trans hw

omit [DecidableEq A] in

theorem coneN_injective {σ τ : Strn A} (h : coneN σ = coneN τ) : σ = τ := by
  have h1 : τ <+: σ := coneN_subset_coneN.mp (le_of_eq h)
  have h2 : σ <+: τ := coneN_subset_coneN.mp (le_of_eq h.symm)
  exact h2.eq_of_length (h2.length_le.antisymm h1.length_le)

theorem coneN_trichotomy (σ τ : Strn A) :
    coneN σ ⊆ coneN τ ∨ coneN τ ⊆ coneN σ ∨ coneN σ ∩ coneN τ = ∅ :=
  if hστ : σ <+: τ then Or.inr (Or.inl (coneN_subset_coneN.mpr hστ))
  else if hτσ : τ <+: σ then Or.inl (coneN_subset_coneN.mpr hτσ)
  else Or.inr (Or.inr (by
    ext w
    simp only [Set.mem_inter_iff, mem_coneN, Set.mem_empty_iff_false, iff_false, not_and]
    intro h1 h2
    rcases List.prefix_or_prefix_of_prefix h1 h2 with h | h
    · exact hστ h
    · exact hτσ h))

/-- Membership in `Cₐ`: a cone `σA*` or a singleton `{σ}`. -/
def memCn (X : Set (Strn A)) : Prop := (∃ σ, X = coneN σ) ∨ (∃ σ, X = {σ})

omit [DecidableEq A] in

theorem memCn_coneN (σ : Strn A) : memCn (coneN σ) := Or.inl ⟨σ, rfl⟩

omit [DecidableEq A] in

theorem memCn_singleton (σ : Strn A) : memCn ({σ} : Set (Strn A)) := Or.inr ⟨σ, rfl⟩

omit [DecidableEq A] in

theorem singleton_subset_coneN {σ τ : Strn A} : ({τ} : Set (Strn A)) ⊆ coneN σ ↔ σ <+: τ := by
  rw [Set.singleton_subset_iff, mem_coneN]

theorem singleton_coneN_nd (σ τ : Strn A) :
    ({τ} : Set (Strn A)) ⊆ coneN σ ∨ coneN σ ⊆ {τ} ∨ ({τ} : Set (Strn A)) ∩ coneN σ = ∅ := by
  by_cases h : σ <+: τ
  · exact Or.inl (singleton_subset_coneN.mpr h)
  · refine Or.inr (Or.inr ?_)
    ext w
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, mem_coneN, Set.mem_empty_iff_false,
      iff_false, not_and]
    rintro rfl hτ
    exact h hτ

theorem nestedOrDisjointN : NestedOrDisjoint (memCn (A := A)) := by
  rintro X Y (⟨σ, rfl⟩ | ⟨σ, rfl⟩) (⟨τ, rfl⟩ | ⟨τ, rfl⟩)
  · exact coneN_trichotomy σ τ
  · rcases singleton_coneN_nd σ τ with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (by rw [Set.inter_comm]; exact h))
  · rcases singleton_coneN_nd τ σ with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · by_cases h : σ = τ
    · subst h; exact Or.inl (Set.Subset.refl _)
    · refine Or.inr (Or.inr ?_)
      ext w
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false,
        not_and]
      rintro rfl h2
      exact h h2

/-- **The generic domain `Cₐ`** of finite-or-infinite `A`-sequences. -/
abbrev Cn (A : Type) [DecidableEq A] : NeighborhoodSystem (Strn A) :=
  NeighborhoodSystem.ofNestedOrDisjoint memCn Set.univ
    ⟨[], Set.mem_univ _⟩ (Or.inl ⟨[], coneN_nil.symm⟩) nestedOrDisjointN
    (fun _ => Set.subset_univ _)

@[simp] theorem Cn_mem {X : Set (Strn A)} : (Cn A).mem X ↔ memCn X := Iff.rfl

@[simp] theorem Cn_master : (Cn A).master = (Set.univ : Set (Strn A)) := rfl

/-- `Cₐ` is `∅`-free: every neighbourhood is non-empty (cones and singletons are inhabited). -/
theorem Cn_nonempty : ∀ X, (Cn A).mem X → X.Nonempty := by
  rintro X (⟨σ, rfl⟩ | ⟨σ, rfl⟩)
  · exact ⟨σ, List.prefix_rfl⟩
  · exact ⟨σ, rfl⟩

/-- `σX = {στ ∣ τ ∈ X}`. -/
def prependN (σ : Strn A) (X : Set (Strn A)) : Set (Strn A) := {w | ∃ τ, τ ∈ X ∧ w = σ ++ τ}

omit [DecidableEq A] in

@[simp] theorem mem_prependN {σ : Strn A} {X : Set (Strn A)} {w : Strn A} :
    w ∈ prependN σ X ↔ ∃ τ, τ ∈ X ∧ w = σ ++ τ := Iff.rfl

omit [DecidableEq A] in

theorem prependN_coneN (σ ρ : Strn A) : prependN σ (coneN ρ) = coneN (σ ++ ρ) := by
  ext w
  simp only [mem_prependN, mem_coneN]
  constructor
  · rintro ⟨τ, hτ, rfl⟩; exact (List.prefix_append_right_inj σ).mpr hτ
  · rintro ⟨t, ht⟩
    exact ⟨ρ ++ t, List.prefix_append ρ t, by rw [← ht, List.append_assoc]⟩

omit [DecidableEq A] in

theorem prependN_mono (σ : Strn A) {X X' : Set (Strn A)} (h : X' ⊆ X) :
    prependN σ X' ⊆ prependN σ X := by
  rintro w ⟨τ, hτ, rfl⟩; exact ⟨τ, h hτ, rfl⟩

omit [DecidableEq A] in

theorem prependN_singleton (σ τ : Strn A) : prependN σ {τ} = {σ ++ τ} := by
  ext w
  simp only [mem_prependN, Set.mem_singleton_iff]
  constructor
  · rintro ⟨t, rfl, rfl⟩; rfl
  · rintro rfl; exact ⟨τ, rfl, rfl⟩

omit [DecidableEq A] in

theorem memCn_prependN (σ : Strn A) {X : Set (Strn A)} (hX : memCn X) : memCn (prependN σ X) := by
  rcases hX with ⟨ρ, rfl⟩ | ⟨ρ, rfl⟩
  · exact Or.inl ⟨σ ++ ρ, prependN_coneN σ ρ⟩
  · exact Or.inr ⟨σ ++ ρ, prependN_singleton σ ρ⟩

/-- **The successor `x ↦ a·x`** prepending the letter `a`: `X (a·x) Y ↔ aX ⊆ Y`. -/
def consMapN (a : A) : ApproximableMap (Cn A) (Cn A) where
  rel X Y := memCn X ∧ memCn Y ∧ prependN [a] X ⊆ Y
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨Or.inl ⟨[], coneN_nil.symm⟩, Or.inl ⟨[], coneN_nil.symm⟩,
    fun _ _ => trivial⟩
  inter_right := by
    rintro X Y Y' ⟨hX, hY, hXY⟩ ⟨_, hY', hXY'⟩
    have hsubInter : prependN [a] X ⊆ Y ∩ Y' := Set.subset_inter hXY hXY'
    have hZ : memCn (prependN [a] X) := memCn_prependN [a] hX
    exact ⟨hX, (Cn A).inter_mem hY hY' hZ hsubInter, hsubInter⟩
  mono := by
    rintro X X' Y Y' ⟨_, _, hXY⟩ hX'X hYY' hX' hY'
    exact ⟨hX', hY', (prependN_mono [a] hX'X).trans (hXY.trans hYY')⟩

@[simp] theorem consMapN_rel {a : A} {X Y : Set (Strn A)} :
    (consMapN a).rel X Y ↔ memCn X ∧ memCn Y ∧ prependN [a] X ⊆ Y := Iff.rfl

section SumSig

universe v

variable {β : Type v} {γ : Type v}

/-- Tokens of the indexed sum `𝟙 + Σ_a β`. -/
abbrev SigTok (A : Type) (β : Type v) := Option (Unit ⊕ (A × β))

end SumSig

/-- The partial element `σ⊥ = ↑σA*`. -/
def strBotN (σ : Strn A) : (Cn A).Element := (Cn A).principal (Cn_mem.mpr (memCn_coneN σ))

theorem consMapN_strBot (a : A) (σ : Strn A) :
    (consMapN a).toElementMap (strBotN σ) = strBotN (a :: σ) := by
  apply NeighborhoodSystem.Element.ext
  intro Y
  constructor
  · rintro ⟨X, ⟨_, hXcone⟩, _, hY, hsub⟩
    refine ⟨hY, ?_⟩
    calc coneN (a :: σ) = prependN [a] (coneN σ) := by rw [prependN_coneN]; rfl
      _ ⊆ prependN [a] X := prependN_mono [a] hXcone
      _ ⊆ Y := hsub
  · rintro ⟨hY, hsub⟩
    refine ⟨coneN σ, ⟨memCn_coneN σ, subset_rfl⟩, memCn_coneN σ, hY, ?_⟩
    rw [show prependN [a] (coneN σ) = coneN (a :: σ) by rw [prependN_coneN]; rfl]
    exact hsub

/-- The total element `σ = ↑{σ}`. -/
def strElemN (σ : Strn A) : (Cn A).Element := (Cn A).principal (Cn_mem.mpr (memCn_singleton σ))

theorem consMapN_strElem (a : A) (σ : Strn A) :
    (consMapN a).toElementMap (strElemN σ) = strElemN (a :: σ) := by
  apply NeighborhoodSystem.Element.ext
  intro Y
  constructor
  · rintro ⟨X, ⟨_, hXsing⟩, _, hY, hsub⟩
    refine ⟨hY, ?_⟩
    calc ({a :: σ} : Set (Strn A)) = prependN [a] {σ} := by rw [prependN_singleton]; rfl
      _ ⊆ prependN [a] X := prependN_mono [a] hXsing
      _ ⊆ Y := hsub
  · rintro ⟨hY, hsub⟩
    refine ⟨{σ}, ⟨memCn_singleton σ, subset_rfl⟩, memCn_singleton σ, hY, ?_⟩
    rw [show prependN [a] ({σ} : Set (Strn A)) = {a :: σ} by rw [prependN_singleton]; rfl]
    exact hsub

section SumSig

universe v

variable {β : Type v} {γ : Type v}

/-- The token `t` in the `a`-indexed copy. -/
def tc (a : A) (t : β) : SigTok A β := some (Sum.inr (a, t))

/-- The `a`-indexed tagged copy `aX`. -/
def jc (a : A) (X : Set β) : Set (SigTok A β) := {w | ∃ t, w = tc a t ∧ t ∈ X}

omit [DecidableEq A] in

theorem tc_injective {a a' : A} {t t' : β} (h : (tc a t : SigTok A β) = tc a' t') :
    a = a' ∧ t = t' := by
  simp only [tc, Option.some.injEq, Sum.inr.injEq, Prod.mk.injEq] at h; exact h

omit [DecidableEq A] in

@[simp] theorem tc_mem_jc {a : A} {X : Set β} {t : β} :
    (tc a t : SigTok A β) ∈ jc a X ↔ t ∈ X := by
  constructor
  · rintro ⟨t', heq, ht'⟩; obtain ⟨-, rfl⟩ := tc_injective heq; exact ht'
  · intro ht; exact ⟨t, rfl, ht⟩

/-- The lone `𝟙`-token. -/
def tu : SigTok A β := some (Sum.inl ())

/-- The `𝟙`-copy neighbourhood (the image of `univ : Set Unit`). -/
def jU : Set (SigTok A β) := {tu}

omit [DecidableEq A] in

@[simp] theorem mem_jU {w : SigTok A β} : w ∈ (jU : Set (SigTok A β)) ↔ w = tu := Iff.rfl

omit [DecidableEq A] in

@[simp] theorem none_not_mem_jU : (none : SigTok A β) ∉ (jU : Set (SigTok A β)) := by
  simp [jU, tu]

omit [DecidableEq A] in

@[simp] theorem none_not_mem_jc {a : A} {X : Set β} : (none : SigTok A β) ∉ jc a X := by
  rintro ⟨t, heq, -⟩; exact absurd heq (by simp [tc])

omit [DecidableEq A] in

@[simp] theorem tu_not_mem_jc {a : A} {X : Set β} : (tu : SigTok A β) ∉ jc a X := by
  rintro ⟨t, heq, -⟩; exact absurd heq (by simp [tu, tc])

omit [DecidableEq A] in

@[simp] theorem tc_not_mem_jU {a : A} {t : β} : (tc a t : SigTok A β) ∉ (jU : Set (SigTok A β)) := by
  simp [jU, tu, tc]

omit [DecidableEq A] in

theorem jU_inter_jc (a : A) (X : Set β) : (jU ∩ jc a X : Set (SigTok A β)) = ∅ := by
  ext w
  simp only [Set.mem_inter_iff, mem_jU, Set.mem_empty_iff_false, iff_false, not_and]
  rintro rfl; exact tu_not_mem_jc

omit [DecidableEq A] in

theorem jU_nonempty : (jU : Set (SigTok A β)).Nonempty := ⟨tu, rfl⟩

omit [DecidableEq A] in

theorem jc_inter_jc_ne {a a' : A} (h : a ≠ a') (X X' : Set β) :
    (jc a X ∩ jc a' X' : Set (SigTok A β)) = ∅ := by
  ext w
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  rintro ⟨t, rfl, -⟩ ⟨t', heq, -⟩
  exact h (tc_injective heq).1

omit [DecidableEq A] in

theorem jc_inter_jc_same (a : A) (X X' : Set β) :
    (jc a X ∩ jc a X' : Set (SigTok A β)) = jc a (X ∩ X') := by
  ext w
  constructor
  · rintro ⟨⟨t, rfl, ht⟩, ⟨t', heq, ht'⟩⟩
    obtain ⟨-, rfl⟩ := tc_injective heq; exact ⟨t, rfl, ht, ht'⟩
  · rintro ⟨t, rfl, ht, ht'⟩; exact ⟨⟨t, rfl, ht⟩, ⟨t, rfl, ht'⟩⟩

omit [DecidableEq A] in

theorem jc_nonempty {a : A} {X : Set β} (hX : X.Nonempty) : (jc a X : Set (SigTok A β)).Nonempty := by
  obtain ⟨t, ht⟩ := hX; exact ⟨tc a t, t, rfl, ht⟩

omit [DecidableEq A] in

theorem jc_subset_jc {a : A} {X X' : Set β} :
    (jc a X : Set (SigTok A β)) ⊆ jc a X' ↔ X ⊆ X' := by
  constructor
  · intro h t ht; exact tc_mem_jc.mp (h (tc_mem_jc.mpr ht))
  · rintro h w ⟨t, rfl, ht⟩; exact tc_mem_jc.mpr (h ht)

omit [DecidableEq A] in

theorem jc_injective {a : A} {X X' : Set β} (h : (jc a X : Set (SigTok A β)) = jc a X') : X = X' :=
  Set.Subset.antisymm (jc_subset_jc.mp h.subset) (jc_subset_jc.mp h.symm.subset)

omit [DecidableEq A] in
/-- Tagged copies determine both index and set: `aX = a'X'` (with `X` non-empty) forces `a=a'`,
`X=X'`. -/
theorem jc_eq_jc {a a' : A} {X X' : Set β} (hXne : X.Nonempty)
    (heq : (jc a X : Set (SigTok A β)) = jc a' X') : a = a' ∧ X = X' := by
  obtain ⟨t, ht⟩ := hXne
  obtain ⟨t', he, -⟩ := heq ▸ (tc_mem_jc.mpr ht)
  obtain ⟨rfl, -⟩ := tc_injective he
  exact ⟨rfl, jc_injective heq⟩

end SumSig

section SumSig

universe v

variable {β : Type v} {γ : Type v}

variable (V : NeighborhoodSystem β)

/-- The master neighbourhood `{Λ} ∪ {tu} ∪ ⋃_a aΔ`. -/
def masterSig : Set (SigTok A β) :=
  {w | w = none ∨ w = tu ∨ ∃ a t, t ∈ V.master ∧ w = tc a t}

end SumSig

section SumSig

universe v

variable {β : Type v} {γ : Type v}

variable (V : NeighborhoodSystem β)

variable {V}

omit [DecidableEq A] in

@[simp] theorem none_mem_masterSig : (none : SigTok A β) ∈ masterSig V := Or.inl rfl

end SumSig

section SumSig

universe v

variable {β : Type v} {γ : Type v}

omit [DecidableEq A] in

theorem tc_mem_jc_ne {a a' : A} (h : a ≠ a') {X : Set β} {t : β} :
    (tc a t : SigTok A β) ∉ jc a' X := by
  rintro ⟨t', heq, -⟩; exact h (tc_injective heq).1

end SumSig

section SumSig

universe v

variable {β : Type v} {γ : Type v}

variable (V : NeighborhoodSystem β)

variable {V}

omit [DecidableEq A] in

@[simp] theorem tu_mem_masterSig : (tu : SigTok A β) ∈ masterSig V := Or.inr (Or.inl rfl)

omit [DecidableEq A] in

theorem eq_masterSig_of_subset {W : Set (SigTok A β)}
    (hsub : masterSig V ⊆ W) (hsub' : W ⊆ masterSig V) : W = masterSig V :=
  Set.Subset.antisymm hsub' hsub

omit [DecidableEq A] in

theorem jU_subset_masterSig : (jU : Set (SigTok A β)) ⊆ masterSig V := by
  rintro w rfl; exact tu_mem_masterSig

omit [DecidableEq A] in

theorem jc_subset_masterSig {a : A} {X : Set β} (hX : V.mem X) :
    (jc a X : Set (SigTok A β)) ⊆ masterSig V := by
  rintro w ⟨t, rfl, ht⟩; exact Or.inr (Or.inr ⟨a, t, V.sub_master hX ht, rfl⟩)

omit [DecidableEq A] in

theorem masterSig_inter_jU : (masterSig V ∩ jU : Set (SigTok A β)) = jU :=
  Set.inter_eq_right.mpr jU_subset_masterSig

omit [DecidableEq A] in

theorem masterSig_inter_jc {a : A} {X : Set β} (hX : V.mem X) :
    (masterSig V ∩ jc a X : Set (SigTok A β)) = jc a X :=
  Set.inter_eq_right.mpr (jc_subset_masterSig hX)

/-- **The `A`-indexed separated sum `𝟙 + Σ_a V`** over `{Λ} ∪ {tu} ∪ ⋃_a aΔ`, under the standing
assumption that no neighbourhood of `V` is empty. The alphabet-generic analogue of `sum3 unitSys V V`
(Example 6.2). -/
def sumSig (A : Type) [DecidableEq A] (V : NeighborhoodSystem β)
    (h : ∀ X, V.mem X → X.Nonempty) :
    NeighborhoodSystem (SigTok A β) where
  mem W := W = masterSig V ∨ W = jU ∨ ∃ a X, V.mem X ∧ W = jc a X
  master := masterSig V
  master_nonempty := ⟨none, none_mem_masterSig⟩
  master_mem := Or.inl rfl
  sub_master := by
    rintro W (rfl | rfl | ⟨a, X, hX, rfl⟩)
    · exact subset_rfl
    · exact jU_subset_masterSig
    · exact jc_subset_masterSig hX
  inter_mem := by
    have hne : ∀ W, (W = masterSig V ∨ W = jU ∨ ∃ a X, V.mem X ∧ W = jc a X) →
        (W : Set (SigTok A β)).Nonempty := by
      rintro W (rfl | rfl | ⟨a, X, hX, rfl⟩)
      · exact ⟨none, none_mem_masterSig⟩
      · exact jU_nonempty
      · exact jc_nonempty (h X hX)
    rintro W W' Z hW hW' hZ hZsub
    rcases hW with rfl | rfl | ⟨a, X, hX, rfl⟩
    · rcases hW' with rfl | rfl | ⟨a', X', hX', rfl⟩
      · rw [Set.inter_self]; exact Or.inl rfl
      · rw [masterSig_inter_jU]; exact Or.inr (Or.inl rfl)
      · rw [masterSig_inter_jc hX']; exact Or.inr (Or.inr ⟨a', X', hX', rfl⟩)
    · rcases hW' with rfl | rfl | ⟨a', X', hX', rfl⟩
      · rw [Set.inter_comm, masterSig_inter_jU]; exact Or.inr (Or.inl rfl)
      · rw [Set.inter_self]; exact Or.inr (Or.inl rfl)
      · rw [jU_inter_jc] at hZsub ⊢
        obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)
    · rcases hW' with rfl | rfl | ⟨a', X', hX', rfl⟩
      · rw [Set.inter_comm, masterSig_inter_jc hX]; exact Or.inr (Or.inr ⟨a, X, hX, rfl⟩)
      · rw [Set.inter_comm, jU_inter_jc] at hZsub ⊢
        obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)
      · by_cases haa : a = a'
        · subst haa
          rw [jc_inter_jc_same] at hZsub ⊢
          rcases hZ with rfl | rfl | ⟨a₂, Z₂, hZ₂, rfl⟩
          · exact absurd (hZsub none_mem_masterSig) (by simp)
          · exact absurd (hZsub (show tu ∈ jU from rfl)) tu_not_mem_jc
          · by_cases ha₂ : a = a₂
            · subst ha₂
              exact Or.inr (Or.inr ⟨a, X ∩ X', V.inter_mem hX hX' hZ₂ (jc_subset_jc.mp hZsub), rfl⟩)
            · obtain ⟨t, ht⟩ := h Z₂ hZ₂
              exact absurd (hZsub (tc_mem_jc.mpr ht)) (tc_mem_jc_ne (Ne.symm ha₂))
        · rw [jc_inter_jc_ne haa] at hZsub ⊢
          obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)

@[simp] theorem sumSig_master {h : ∀ X, V.mem X → X.Nonempty} :
    (sumSig A V h).master = masterSig V := rfl

end SumSig

section SumSig

universe v

variable {β : Type v} {γ : Type v}

variable (V : NeighborhoodSystem β)

variable {V}

variable {h : ∀ X, V.mem X → X.Nonempty}

/-- A `sumSig`-neighbourhood contained in the `𝟙`-copy `jU` is `jU`. -/
theorem mem_subset_jU_inv {W : Set (SigTok A β)}
    (hW : (sumSig A V h).mem W) (hsub : W ⊆ jU) : W = jU := by
  rcases hW with rfl | rfl | ⟨a', X₂, hX₂, rfl⟩
  · exact absurd (hsub none_mem_masterSig) none_not_mem_jU
  · rfl
  · obtain ⟨t, ht⟩ := h X₂ hX₂
    exact absurd (hsub (tc_mem_jc.mpr ht)) tc_not_mem_jU

/-- A `sumSig`-neighbourhood contained in an `a`-copy `aX` is itself an `a`-copy. -/
theorem mem_subset_jc_inv {W : Set (SigTok A β)} {a : A} {X : Set β}
    (hW : (sumSig A V h).mem W) (hsub : W ⊆ jc a X) : ∃ X₂, V.mem X₂ ∧ W = jc a X₂ := by
  rcases hW with rfl | rfl | ⟨a', X₂, hX₂, rfl⟩
  · exact absurd (hsub none_mem_masterSig) none_not_mem_jc
  · exact absurd (hsub (show tu ∈ jU from rfl)) tu_not_mem_jc
  · obtain ⟨t, ht⟩ := h X₂ hX₂
    obtain ⟨t', heq, -⟩ := hsub (tc_mem_jc.mpr ht)
    obtain ⟨rfl, -⟩ := tc_injective heq
    exact ⟨X₂, hX₂, rfl⟩

/-- The `a`-th copy injection `V ↪ 𝟙+Σ_a V`: send `x∈|V|` to the sum element whose proper
neighbourhoods are the `a`-copies `aX` with `X∈x`. -/
def sinjC (a : A) (x : V.Element) : (sumSig A V h).Element where
  mem W := W = masterSig V ∨ ∃ X, V.mem X ∧ W = jc a X ∧ x.mem X
  sub := by
    rintro W (rfl | ⟨X, hX, rfl, -⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨a, X, hX, rfl⟩)
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hx⟩) (rfl | ⟨X', hX', rfl, hx'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr ⟨X', hX', by rw [masterSig_inter_jc hX'], hx'⟩
    · exact Or.inr ⟨X, hX, by rw [Set.inter_comm, masterSig_inter_jc hX], hx⟩
    · exact Or.inr ⟨X ∩ X', x.sub (x.inter_mem hx hx'), jc_inter_jc_same a X X', x.inter_mem hx hx'⟩
  up_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hx⟩) hW' hsub
    · exact Or.inl (eq_masterSig_of_subset hsub ((sumSig A V h).sub_master hW'))
    · rcases hW' with rfl | rfl | ⟨a', X', hX', rfl⟩
      · exact Or.inl rfl
      · obtain ⟨t, ht⟩ := h X (x.sub hx)
        exact absurd (hsub (tc_mem_jc.mpr ht)) tc_not_mem_jU
      · obtain ⟨t, ht⟩ := h X (x.sub hx)
        obtain ⟨t', heq, -⟩ := hsub (tc_mem_jc.mpr ht)
        obtain ⟨rfl, -⟩ := tc_injective heq
        exact Or.inr ⟨X', hX', rfl, x.up_mem hx hX' (jc_subset_jc.mp hsub)⟩

/-- The basepoint/`𝟙`-injection: the image of the unique point of `𝟙`. Its proper neighbourhood is
the `𝟙`-copy `jU`. -/
def sinjU : (sumSig A V h).Element where
  mem W := W = masterSig V ∨ W = jU
  sub := by
    rintro W (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | rfl) (rfl | rfl)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr (by rw [masterSig_inter_jU])
    · exact Or.inr (by rw [Set.inter_comm, masterSig_inter_jU])
    · exact Or.inr (by rw [Set.inter_self])
  up_mem := by
    rintro W W' (rfl | rfl) hW' hsub
    · exact Or.inl (eq_masterSig_of_subset hsub ((sumSig A V h).sub_master hW'))
    · rcases hW' with rfl | rfl | ⟨a', X', hX', rfl⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd (hsub (show tu ∈ jU from rfl)) tu_not_mem_jc

@[simp] theorem sinjU_mem_jU : (sinjU (h := h)).mem (jU : Set (SigTok A β)) := Or.inr rfl

@[simp] theorem sinjC_mem_jc {a : A} {x : V.Element} {X : Set β} (hX : V.mem X) :
    (sinjC (h := h) a x).mem (jc a X) ↔ x.mem X := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hx⟩)
    · exact absurd (h0 ▸ none_mem_masterSig) none_not_mem_jc
    · rw [jc_injective heq]; exact hx
  · intro hx; exact Or.inr ⟨X, hX, rfl, hx⟩

theorem sinjC_mono {a : A} {x x' : V.Element} (hxle : x ≤ x') :
    sinjC (h := h) a x ≤ sinjC a x' := by
  rintro W (rfl | ⟨X, hX, rfl, hm⟩)
  · exact Or.inl rfl
  · exact Or.inr ⟨X, hX, rfl, hxle X hm⟩

end SumSig

section SumMapSig

universe v

variable {β₀ β₁ β₂ : Type v}
  {V₀ : NeighborhoodSystem β₀} {V₁ : NeighborhoodSystem β₁} {V₂ : NeighborhoodSystem β₂}
  {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
  {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty}

/-- **The indexed sum map `Σf = I_𝟙 + Σ_a f`** acting as the identity on the `𝟙`-summand and as `f`
on each `a`-copy. The generic analogue of `sumMap3 (idMap unitSys) f f`. -/
def sumMapSig (f : ApproximableMap V₀ V₁) :
    ApproximableMap (sumSig A V₀ h₀) (sumSig A V₁ h₁) where
  rel W W' := (sumSig A V₀ h₀).mem W ∧ (sumSig A V₁ h₁).mem W' ∧
    (W' = masterSig V₁ ∨ (W = jU ∧ W' = jU) ∨
      ∃ a X Y', W = jc a X ∧ W' = jc a Y' ∧ f.rel X Y')
  rel_dom hr := hr.1
  rel_cod hr := hr.2.1
  master_rel := ⟨(sumSig A V₀ h₀).master_mem, (sumSig A V₁ h₁).master_mem, Or.inl rfl⟩
  inter_right := by
    rintro W W'₁ W'₂ ⟨hW, hW'₁, hd₁⟩ ⟨-, hW'₂, hd₂⟩
    have hmem : ∀ W'' : Set (SigTok A β₁),
        (W'' = masterSig V₁ ∨ (W = jU ∧ W'' = jU) ∨
          ∃ a X Y', W = jc a X ∧ W'' = jc a Y' ∧ f.rel X Y') → (sumSig A V₁ h₁).mem W'' := by
      rintro W'' (rfl | ⟨-, rfl⟩ | ⟨a, X, Y', -, rfl, hf⟩)
      · exact (sumSig A V₁ h₁).master_mem
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ⟨a, Y', f.rel_cod hf, rfl⟩)
    have key : (W'₁ ∩ W'₂ = masterSig V₁ ∨ (W = jU ∧ W'₁ ∩ W'₂ = jU) ∨
        ∃ a X Y', W = jc a X ∧ W'₁ ∩ W'₂ = jc a Y' ∧ f.rel X Y') := by
      rcases hd₁ with rfl | ⟨hWU, rfl⟩ | ⟨a, X, Y'₁, hWX, rfl, hf₁⟩
      · rw [Set.inter_eq_right.mpr (show W'₂ ⊆ masterSig V₁ from
          (sumSig A V₁ h₁).sub_master hW'₂)]; exact hd₂
      · rcases hd₂ with rfl | ⟨-, rfl⟩ | ⟨a, X, Y', hWX, rfl, hf⟩
        · rw [Set.inter_eq_left.mpr jU_subset_masterSig]; exact Or.inr (Or.inl ⟨hWU, rfl⟩)
        · rw [Set.inter_self]; exact Or.inr (Or.inl ⟨hWU, rfl⟩)
        · obtain ⟨t, ht⟩ := h₀ X (f.rel_dom hf)
          exact absurd ((hWX.symm.trans hWU) ▸ tc_mem_jc.mpr ht) tc_not_mem_jU
      · rcases hd₂ with rfl | ⟨hWU2, rfl⟩ | ⟨a', X', Y'₂, hWX', rfl, hf₂⟩
        · rw [Set.inter_eq_left.mpr (jc_subset_masterSig (f.rel_cod hf₁))]
          exact Or.inr (Or.inr ⟨a, X, Y'₁, hWX, rfl, hf₁⟩)
        · obtain ⟨t, ht⟩ := h₀ X (f.rel_dom hf₁)
          exact absurd ((hWX.symm.trans hWU2) ▸ tc_mem_jc.mpr ht) tc_not_mem_jU
        · obtain ⟨rfl, rfl⟩ := jc_eq_jc (h₀ X (f.rel_dom hf₁)) (hWX.symm.trans hWX')
          rw [jc_inter_jc_same]
          exact Or.inr (Or.inr ⟨a, X, Y'₁ ∩ Y'₂, hWX, rfl, f.inter_right hf₁ hf₂⟩)
    exact ⟨hW, hmem _ key, key⟩
  mono := by
    rintro W W₂ W' W'₂ ⟨hW, hW', hd⟩ hW₂W hW'W'₂ hW₂mem hW'₂mem
    refine ⟨hW₂mem, hW'₂mem, ?_⟩
    rcases hd with rfl | ⟨rfl, rfl⟩ | ⟨a, X, Y', rfl, rfl, hf⟩
    · exact Or.inl (eq_masterSig_of_subset hW'W'₂ ((sumSig A V₁ h₁).sub_master hW'₂mem))
    · have hW₂jU : W₂ = jU := mem_subset_jU_inv hW₂mem hW₂W
      rcases hW'₂mem with rfl | rfl | ⟨a', Y'₂, hY'₂, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨hW₂jU, rfl⟩)
      · exact absurd (hW'W'₂ (show tu ∈ jU from rfl)) tu_not_mem_jc
    · obtain ⟨X₂, hX₂, rfl⟩ := mem_subset_jc_inv hW₂mem hW₂W
      have hX₂X : X₂ ⊆ X := jc_subset_jc.mp hW₂W
      rcases hW'₂mem with rfl | rfl | ⟨a', Y'₂, hY'₂, rfl⟩
      · exact Or.inl rfl
      · obtain ⟨t, ht⟩ := h₁ Y' (f.rel_cod hf)
        exact absurd (hW'W'₂ (tc_mem_jc.mpr ht)) tc_not_mem_jU
      · obtain ⟨t, ht⟩ := h₁ Y' (f.rel_cod hf)
        obtain ⟨t', he, -⟩ := hW'W'₂ (tc_mem_jc.mpr ht)
        obtain ⟨rfl, -⟩ := tc_injective he
        exact Or.inr (Or.inr ⟨a, X₂, Y'₂, rfl, rfl,
          f.mono hf hX₂X (jc_subset_jc.mp hW'W'₂) hX₂ hY'₂⟩)

/-- The sum map is strict: it sends `⊥ = master` only to `master`. -/
theorem isStrict_sumMapSig (f : ApproximableMap V₀ V₁) :
    IsStrict (sumMapSig (A := A) (h₀ := h₀) (h₁ := h₁) f) := by
  rintro W' ⟨-, -, hd⟩
  rcases hd with rfl | ⟨hWU, -⟩ | ⟨a, X, Y', hWX, -, -⟩
  · rfl
  · exact absurd (hWU ▸ (show (none : SigTok A β₀) ∈ (sumSig A V₀ h₀).master from
      none_mem_masterSig)) none_not_mem_jU
  · exact absurd (hWX ▸ (show (none : SigTok A β₀) ∈ (sumSig A V₀ h₀).master from
      none_mem_masterSig)) none_not_mem_jc

@[simp] theorem sumMapSig_rel {f : ApproximableMap V₀ V₁} {W W'} :
    (sumMapSig (A := A) (h₀ := h₀) (h₁ := h₁) f).rel W W' ↔
      (sumSig A V₀ h₀).mem W ∧ (sumSig A V₁ h₁).mem W' ∧
        (W' = masterSig V₁ ∨ (W = jU ∧ W' = jU) ∨
          ∃ a X Y', W = jc a X ∧ W' = jc a Y' ∧ f.rel X Y') := Iff.rfl

/-- **Functoriality (composition): `Σ(g∘f) = Σg ∘ Σf`.** -/
theorem sumMapSig_comp (g : ApproximableMap V₁ V₂) (f : ApproximableMap V₀ V₁) :
    sumMapSig (A := A) (h₀ := h₀) (h₁ := h₂) (g.comp f)
      = (sumMapSig (A := A) (h₀ := h₁) (h₁ := h₂) g).comp
          (sumMapSig (A := A) (h₀ := h₀) (h₁ := h₁) f) := by
  apply ApproximableMap.ext
  intro W W''
  constructor
  · rintro ⟨hW, hW'', hd⟩
    rcases hd with rfl | ⟨hWU, rfl⟩ | ⟨a, X, Z'', rfl, rfl, Y', hf, hg⟩
    · exact ⟨masterSig V₁, ⟨hW, (sumSig A V₁ h₁).master_mem, Or.inl rfl⟩,
        (sumSig A V₁ h₁).master_mem, hW'', Or.inl rfl⟩
    · exact ⟨jU, ⟨hW, Or.inr (Or.inl rfl), Or.inr (Or.inl ⟨hWU, rfl⟩)⟩,
        Or.inr (Or.inl rfl), hW'', Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    · exact ⟨jc a Y', ⟨hW, Or.inr (Or.inr ⟨a, Y', f.rel_cod hf, rfl⟩),
        Or.inr (Or.inr ⟨a, X, Y', rfl, rfl, hf⟩)⟩,
        Or.inr (Or.inr ⟨a, Y', f.rel_cod hf, rfl⟩), hW'',
        Or.inr (Or.inr ⟨a, Y', Z'', rfl, rfl, hg⟩)⟩
  · rintro ⟨W', ⟨hW, hW', hdf⟩, -, hW'', hdg⟩
    refine ⟨hW, hW'', ?_⟩
    rcases hdg with rfl | ⟨hW'U, rfl⟩ | ⟨a, Y', Z'', hW'Y', rfl, hg⟩
    · exact Or.inl rfl
    · rcases hdf with rfl | ⟨hWU, -⟩ | ⟨a, X, Y'₀, -, hW'eq, hf⟩
      · exact absurd ((hW'U.symm) ▸ none_mem_masterSig) none_not_mem_jU
      · exact Or.inr (Or.inl ⟨hWU, rfl⟩)
      · obtain ⟨t, ht⟩ := h₁ Y'₀ (f.rel_cod hf)
        exact absurd ((hW'eq.symm.trans hW'U) ▸ tc_mem_jc.mpr ht) tc_not_mem_jU
    · rcases hdf with rfl | ⟨-, hW'U⟩ | ⟨a', X, Y'₀, rfl, hW'eq, hf⟩
      · exact absurd ((hW'Y'.symm) ▸ none_mem_masterSig) none_not_mem_jc
      · obtain ⟨t, ht⟩ := h₁ Y' (g.rel_dom hg)
        exact absurd ((hW'U.symm.trans hW'Y') ▸ tc_mem_jc.mpr ht) tc_not_mem_jU
      · obtain ⟨rfl, rfl⟩ := jc_eq_jc (h₁ Y'₀ (f.rel_cod hf)) (hW'eq.symm.trans hW'Y')
        exact Or.inr (Or.inr ⟨a', X, Z'', rfl, rfl, ⟨Y'₀, hf, hg⟩⟩)

/-- **Functoriality (identities): `Σ(I) = I`.** -/
theorem sumMapSig_id :
    sumMapSig (A := A) (V₀ := V₀) (V₁ := V₀) (h₀ := h₀) (h₁ := h₀) (idMap V₀)
      = idMap (sumSig A V₀ h₀) := by
  apply ApproximableMap.ext
  intro W W'
  constructor
  · rintro ⟨hW, hW', hd⟩
    refine ⟨hW, hW', ?_⟩
    rcases hd with rfl | ⟨rfl, rfl⟩ | ⟨a, X, Y', rfl, rfl, -, -, hXY⟩
    · exact (sumSig A V₀ h₀).sub_master hW
    · exact subset_rfl
    · exact jc_subset_jc.mpr hXY
  · rintro ⟨hW, hW', hsub⟩
    refine ⟨hW, hW', ?_⟩
    rcases hW with rfl | rfl | ⟨a, X, hX, rfl⟩
    · exact Or.inl (eq_masterSig_of_subset hsub ((sumSig A V₀ h₀).sub_master hW'))
    · rcases hW' with rfl | rfl | ⟨a', X', hX', rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact absurd (hsub (show tu ∈ jU from rfl)) tu_not_mem_jc
    · rcases hW' with rfl | rfl | ⟨a', X', hX', rfl⟩
      · exact Or.inl rfl
      · obtain ⟨t, ht⟩ := h₀ X hX; exact absurd (hsub (tc_mem_jc.mpr ht)) tc_not_mem_jU
      · obtain ⟨t, ht⟩ := h₀ X hX
        obtain ⟨t', he, -⟩ := hsub (tc_mem_jc.mpr ht)
        obtain ⟨rfl, -⟩ := tc_injective he
        exact Or.inr (Or.inr ⟨a, X, X', rfl, rfl, hX, hX', jc_subset_jc.mp hsub⟩)

/-- `Σf` on the `a`-copy injection: `(Σf)(inj_a x) = inj_a (f x)`. -/
theorem sumMapSig_sinjC (f : ApproximableMap V₀ V₁) (a : A) (x : V₀.Element) :
    (sumMapSig (A := A) (h₀ := h₀) (h₁ := h₁) f).toElementMap (sinjC (h := h₀) a x)
      = sinjC (h := h₁) a (f.toElementMap x) := by
  apply NeighborhoodSystem.Element.ext
  intro W'
  constructor
  · rintro ⟨U, hU, -, -, hd⟩
    rcases hd with rfl | ⟨hUjU, rfl⟩ | ⟨a', X, Y', hUj, rfl, hf⟩
    · exact Or.inl rfl
    · rcases hU with hUm | ⟨X₀, hX₀, hUeq, hx⟩
      · exact absurd ((hUm.symm.trans hUjU) ▸ none_mem_masterSig) none_not_mem_jU
      · obtain ⟨t, ht⟩ := h₀ X₀ hX₀
        exact absurd ((hUeq.symm.trans hUjU) ▸ tc_mem_jc.mpr ht) tc_not_mem_jU
    · rcases hU with hUm | ⟨X₀, hX₀, hUeq, hx⟩
      · exact absurd ((hUm.symm.trans hUj) ▸ none_mem_masterSig) none_not_mem_jc
      · obtain ⟨rfl, rfl⟩ := jc_eq_jc (h₀ X₀ hX₀) (hUeq.symm.trans hUj)
        exact Or.inr ⟨Y', f.rel_cod hf, rfl, ⟨X₀, hx, hf⟩⟩
  · rintro (rfl | ⟨Y', hY', rfl, hm⟩)
    · exact ⟨masterSig V₀, Or.inl rfl, (sumSig A V₀ h₀).master_mem,
        (sumSig A V₁ h₁).master_mem, Or.inl rfl⟩
    · obtain ⟨X, hx, hf⟩ := hm
      exact ⟨jc a X, Or.inr ⟨X, x.sub hx, rfl, hx⟩, Or.inr (Or.inr ⟨a, X, x.sub hx, rfl⟩),
        Or.inr (Or.inr ⟨a, Y', f.rel_cod hf, rfl⟩), Or.inr (Or.inr ⟨a, X, Y', rfl, rfl, hf⟩)⟩

/-- `Σf` fixes the basepoint injection. -/
theorem sumMapSig_sinjU (f : ApproximableMap V₀ V₁) :
    (sumMapSig (A := A) (h₀ := h₀) (h₁ := h₁) f).toElementMap (sinjU (h := h₀))
      = sinjU (h := h₁) := by
  apply NeighborhoodSystem.Element.ext
  intro W'
  constructor
  · rintro ⟨U, hU, -, -, hd⟩
    rcases hd with rfl | ⟨-, rfl⟩ | ⟨a, X, Y', hUj, rfl, hf⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
    · rcases hU with hUm | rfl
      · exact absurd ((hUm.symm.trans hUj) ▸ none_mem_masterSig) none_not_mem_jc
      · exact absurd (hUj ▸ (show tu ∈ jU from rfl)) tu_not_mem_jc
  · rintro (rfl | rfl)
    · exact ⟨masterSig V₀, Or.inl rfl, (sumSig A V₀ h₀).master_mem,
        (sumSig A V₁ h₁).master_mem, Or.inl rfl⟩
    · exact ⟨jU, Or.inr rfl, Or.inr (Or.inl rfl), Or.inr (Or.inl rfl),
        Or.inr (Or.inl ⟨rfl, rfl⟩)⟩

end SumMapSig

section SumSig

universe v

variable {β : Type v} {γ : Type v}

variable (V : NeighborhoodSystem β)

variable {V}

theorem sumSig_nonempty {h : ∀ X, V.mem X → X.Nonempty} :
    ∀ W, (sumSig A V h).mem W → W.Nonempty := by
  rintro W (rfl | rfl | ⟨a, X, hX, rfl⟩)
  · exact ⟨none, none_mem_masterSig⟩
  · exact jU_nonempty
  · exact jc_nonempty (h X hX)

end SumSig

/-- `Tsig` on objects: `Tsig(D) = 𝟙 + Σ_a D`, again `∅`-free (`sumSig_nonempty`). -/
abbrev tsigObj (A : Type) [DecidableEq A] (D : StrictDomainObj.{0}) : StrictDomainObj.{0} where
  carrier := SigTok A D.carrier
  sys := sumSig A D.sys D.nonempty
  nonempty := sumSig_nonempty

@[simp] theorem tsigObj_sys (A : Type) [DecidableEq A] (D : StrictDomainObj.{0}) :
    (tsigObj A D).sys = sumSig A D.sys D.nonempty := rfl

/-- `Tsig` on maps: `Tsig(f) = I_𝟙 + Σ_a f`, strict by `isStrict_sumMapSig`. -/
def tsigMapHom (A : Type) [DecidableEq A] {D E : StrictDomainObj.{0}} (f : (D ⟶ E)) :
    ((tsigObj A D) ⟶ (tsigObj A E)) :=
  ⟨sumMapSig (A := A) (h₀ := D.nonempty) (h₁ := E.nonempty) f.1, isStrict_sumMapSig _⟩

@[simp] theorem tsigMapHom_val (A : Type) [DecidableEq A] {D E : StrictDomainObj.{0}}
    (f : (D ⟶ E)) :
    (tsigMapHom A f).1 = sumMapSig (A := A) (h₀ := D.nonempty) (h₁ := E.nonempty) f.1 := rfl

/-- **The functor `Tsig(X) = 𝟙 + Σ_{a:A} X`** on the category of `∅`-free domains and strict maps. -/
abbrev Tsig (A : Type) [DecidableEq A] : Endofunctor StrictDomainObj.{0} where
  obj := tsigObj A
  map := tsigMapHom A
  map_id _ := Subtype.ext sumMapSig_id
  map_comp {_ _ _} g f := Subtype.ext (sumMapSig_comp g.1 f.1)

@[simp] theorem Tsig_obj (A : Type) [DecidableEq A] (D : StrictDomainObj.{0}) :
    (Tsig A).obj D = tsigObj A D := rfl

@[simp] theorem Tsig_map_val (A : Type) [DecidableEq A] {D E : StrictDomainObj.{0}}
    (f : (D ⟶ E)) :
    ((Tsig A).map f).1 = sumMapSig (A := A) (h₀ := D.nonempty) (h₁ := E.nonempty) f.1 := rfl

section Iso

variable {A : Type} [DecidableEq A] [Inhabited A]

/-- `aX = {a :: w' ∣ w' ∈ X}`: the `a`-prefixed copy of a neighbourhood. -/
def embA (a : A) (X : Set (Strn A)) : Set (Strn A) := {w | ∃ w', w = a :: w' ∧ w' ∈ X}

omit [DecidableEq A] [Inhabited A] in

@[simp] theorem mem_embA {a : A} {X : Set (Strn A)} {w : Strn A} :
    w ∈ embA a X ↔ ∃ w', w = a :: w' ∧ w' ∈ X := Iff.rfl

/-- The right-hand side of the domain equation: the `A`-indexed sum `𝟙 + Σ_a Cₐ`. -/
abbrev CCn (A : Type) [DecidableEq A] : NeighborhoodSystem (SigTok A (Strn A)) :=
  sumSig A (Cn A) Cn_nonempty

omit [DecidableEq A] [Inhabited A] in

theorem embA_eq_prependN (a : A) (X : Set (Strn A)) : embA a X = prependN [a] X := by
  ext w
  simp only [mem_embA, mem_prependN]
  constructor
  · rintro ⟨w', rfl, hX⟩; exact ⟨w', hX, rfl⟩
  · rintro ⟨t, hX, rfl⟩; exact ⟨t, rfl, hX⟩

omit [DecidableEq A] [Inhabited A] in

theorem embA_coneN (a : A) (σ : Strn A) : embA a (coneN σ) = coneN (a :: σ) := by
  rw [embA_eq_prependN, prependN_coneN]; rfl

omit [DecidableEq A] [Inhabited A] in

theorem embA_inter (a : A) (X X' : Set (Strn A)) : embA a X ∩ embA a X' = embA a (X ∩ X') := by
  ext w
  simp only [Set.mem_inter_iff, mem_embA]
  constructor
  · rintro ⟨⟨w', rfl, hX⟩, w'', heq, hX'⟩
    rw [List.cons.injEq] at heq; obtain ⟨-, rfl⟩ := heq; exact ⟨w', rfl, hX, hX'⟩
  · rintro ⟨w', rfl, hX, hX'⟩; exact ⟨⟨w', rfl, hX⟩, ⟨w', rfl, hX'⟩⟩

omit [DecidableEq A] [Inhabited A] in

theorem embA_inter_ne {a a' : A} (h : a ≠ a') (X Y : Set (Strn A)) :
    embA a X ∩ embA a' Y = ∅ := by
  ext w
  simp only [Set.mem_inter_iff, mem_embA, Set.mem_empty_iff_false, iff_false, not_and]
  rintro ⟨w', rfl, -⟩ ⟨w'', heq, -⟩
  rw [List.cons.injEq] at heq; exact h heq.1

omit [DecidableEq A] [Inhabited A] in

theorem embA_singleton (a : A) (σ : Strn A) : embA a ({σ} : Set (Strn A)) = {a :: σ} := by
  rw [embA_eq_prependN, prependN_singleton]; rfl

omit [DecidableEq A] [Inhabited A] in

theorem embA_subset {a : A} {X X' : Set (Strn A)} : embA a X ⊆ embA a X' ↔ X ⊆ X' := by
  constructor
  · intro h w' hw'
    obtain ⟨w'', heq, hX'⟩ := h ⟨w', rfl, hw'⟩
    rw [List.cons.injEq] at heq; obtain ⟨-, rfl⟩ := heq; exact hX'
  · rintro h w ⟨w', rfl, hX⟩; exact ⟨w', rfl, h hX⟩

omit [DecidableEq A] [Inhabited A] in

theorem embA_injective {a : A} {X X' : Set (Strn A)} (h : embA a X = embA a X') : X = X' :=
  Set.Subset.antisymm (embA_subset.mp h.subset) (embA_subset.mp h.symm.subset)

omit [DecidableEq A] [Inhabited A] in
/-- **The shape of a `Cₐ`-neighbourhood.** Every neighbourhood is the master `Σ*`, the terminator
`{Λ}`, or an `a`-copy `aX` with `X ∈ Cₐ`. -/
theorem memCn_cases {W : Set (Strn A)} (hW : memCn W) :
    W = Set.univ ∨ W = ({[]} : Set (Strn A)) ∨ ∃ a X, memCn X ∧ W = embA a X := by
  rcases hW with ⟨σ, rfl⟩ | ⟨σ, rfl⟩
  · cases σ with
    | nil => exact Or.inl coneN_nil
    | cons a σ' => exact Or.inr (Or.inr ⟨a, coneN σ', memCn_coneN σ', (embA_coneN a σ').symm⟩)
  · cases σ with
    | nil => exact Or.inr (Or.inl rfl)
    | cons a σ' => exact Or.inr (Or.inr ⟨a, {σ'}, memCn_singleton σ', (embA_singleton a σ').symm⟩)

omit [Inhabited A] in

omit [DecidableEq A] in

theorem memCn_embA (a : A) {X : Set (Strn A)} (hX : memCn X) : memCn (embA a X) := by
  rw [embA_eq_prependN]; exact memCn_prependN [a] hX

omit [DecidableEq A] [Inhabited A] in

theorem memCn_embA_inv {a : A} {W : Set (Strn A)} (h : memCn (embA a W)) : memCn W := by
  rcases h with ⟨σ, hσ⟩ | ⟨σ, hσ⟩
  · have hmem : σ ∈ embA a W := hσ ▸ (show σ ∈ coneN σ from List.prefix_rfl)
    obtain ⟨w', rfl, -⟩ := hmem
    rw [← embA_coneN] at hσ; rw [embA_injective hσ]; exact memCn_coneN w'
  · have hmem : σ ∈ embA a W := hσ ▸ (Set.mem_singleton_iff.mpr rfl : σ ∈ ({σ} : Set (Strn A)))
    obtain ⟨w', rfl, -⟩ := hmem
    rw [← embA_singleton] at hσ; rw [embA_injective hσ]; exact memCn_singleton w'

omit [DecidableEq A] [Inhabited A] in

theorem nil_not_mem_embA {a : A} {X : Set (Strn A)} : ([] : Strn A) ∉ embA a X := by
  rintro ⟨w', heq, -⟩; exact absurd heq (by simp)

omit [DecidableEq A] [Inhabited A] in

theorem embA_ne_univ (a : A) (X : Set (Strn A)) : embA a X ≠ Set.univ := by
  intro h; exact nil_not_mem_embA (X := X) (a := a) (by rw [h]; trivial)

omit [DecidableEq A] [Inhabited A] in

theorem singleton_nil_inter_embA (a : A) (X : Set (Strn A)) :
    (({[]} : Set (Strn A)) ∩ embA a X) = ∅ := by
  ext w
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff, mem_embA, Set.mem_empty_iff_false,
    iff_false, not_and]
  rintro rfl ⟨w', heq, -⟩; exact absurd heq (by simp)

omit [DecidableEq A] [Inhabited A] in

theorem singleton_nil_ne_embA (a : A) (X : Set (Strn A)) :
    ({[]} : Set (Strn A)) ≠ embA a X := by
  intro h
  exact nil_not_mem_embA (h ▸ (Set.mem_singleton_iff.mpr rfl : ([] : Strn A) ∈ ({[]} : Set (Strn A))))

omit [DecidableEq A] in

theorem singleton_nil_ne_univ : ({[]} : Set (Strn A)) ≠ Set.univ := by
  intro h
  have hmem : ([default] : Strn A) ∈ ({[]} : Set (Strn A)) := by rw [h]; trivial
  rw [Set.mem_singleton_iff] at hmem; exact absurd hmem (by simp)

omit [Inhabited A] in

theorem sumSig_mem_jc_inv {a : A} {X : Set (Strn A)} (h : (CCn A).mem (jc a X)) :
    (Cn A).mem X := by
  rcases h with h0 | hU | ⟨a', X', hX', heq⟩
  · exact absurd (h0 ▸ none_mem_masterSig) none_not_mem_jc
  · have : (tu : SigTok A (Strn A)) ∈ jc a X := by rw [hU]; rfl
    exact absurd this tu_not_mem_jc
  · by_cases haa : a = a'
    · subst haa; rw [jc_injective heq]; exact hX'
    · obtain ⟨t, ht⟩ := Cn_nonempty X' hX'
      exact absurd (heq.symm ▸ (tc_mem_jc.mpr ht)) (tc_mem_jc_ne (Ne.symm haa))

/-- **Forward half of `Cₐ ≅ 𝟙 + Σ_a Cₐ`.** Records, for each branch, whether `x` finishes at `Λ`
(the `𝟙`-summand) or reaches the `a`-copy `aX` (the `a`-th summand). -/
def toCC (x : (Cn A).Element) : (CCn A).Element where
  mem W := W = masterSig (Cn A)
    ∨ (W = jU ∧ x.mem ({[]} : Set (Strn A)))
    ∨ (∃ a X, (Cn A).mem X ∧ W = jc a X ∧ x.mem (embA a X))
  sub := by
    rintro W (rfl | ⟨rfl, -⟩ | ⟨a, X, hX, rfl, -⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨a, X, hX, rfl⟩)
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨rfl, hzU⟩ | ⟨a, X, hX, rfl, hzF⟩)
      (rfl | ⟨rfl, hzU'⟩ | ⟨a', X', hX', rfl, hzF'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr (Or.inl ⟨by rw [masterSig_inter_jU], hzU'⟩)
    · exact Or.inr (Or.inr ⟨a', X', hX', by rw [masterSig_inter_jc hX'], hzF'⟩)
    · exact Or.inr (Or.inl ⟨by rw [Set.inter_comm, masterSig_inter_jU], hzU⟩)
    · exact Or.inr (Or.inl ⟨by rw [Set.inter_self], hzU⟩)
    · exfalso
      have hx := x.inter_mem hzU hzF'; rw [singleton_nil_inter_embA] at hx
      obtain ⟨t, ht⟩ := Cn_nonempty _ (x.sub hx); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr ⟨a, X, hX, by rw [Set.inter_comm, masterSig_inter_jc hX], hzF⟩)
    · exfalso
      have hx := x.inter_mem hzF hzU'; rw [Set.inter_comm, singleton_nil_inter_embA] at hx
      obtain ⟨t, ht⟩ := Cn_nonempty _ (x.sub hx); exact Set.notMem_empty t ht
    · by_cases haa : a = a'
      · subst haa
        have hx := x.inter_mem hzF hzF'; rw [embA_inter] at hx
        exact Or.inr (Or.inr ⟨a, X ∩ X', memCn_embA_inv (x.sub hx), jc_inter_jc_same a X X', hx⟩)
      · exfalso
        have hx := x.inter_mem hzF hzF'; rw [embA_inter_ne haa] at hx
        obtain ⟨t, ht⟩ := Cn_nonempty _ (x.sub hx); exact Set.notMem_empty t ht
  up_mem := by
    rintro W W' (rfl | ⟨rfl, hzU⟩ | ⟨a, X, hX, rfl, hzF⟩) hW' hsub
    · exact Or.inl (eq_masterSig_of_subset hsub ((CCn A).sub_master hW'))
    · rcases hW' with rfl | rfl | ⟨a', X', hX', rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨rfl, hzU⟩)
      · exact absurd (hsub (show tu ∈ jU from rfl)) tu_not_mem_jc
    · rcases hW' with rfl | rfl | ⟨a', X', hX', rfl⟩
      · exact Or.inl rfl
      · obtain ⟨t, ht⟩ := Cn_nonempty X hX
        exact absurd (hsub (tc_mem_jc.mpr ht)) tc_not_mem_jU
      · obtain ⟨t, ht⟩ := Cn_nonempty X hX
        obtain ⟨t', he, -⟩ := hsub (tc_mem_jc.mpr ht)
        obtain ⟨rfl, -⟩ := tc_injective he
        exact Or.inr (Or.inr ⟨a, X', hX', rfl,
          x.up_mem hzF (memCn_embA a hX') (embA_subset.mpr (jc_subset_jc.mp hsub))⟩)

omit [Inhabited A] in

@[simp] theorem toCC_mem_jU {x : (Cn A).Element} :
    (toCC x).mem (jU : Set (SigTok A (Strn A))) ↔ x.mem ({[]} : Set (Strn A)) := by
  constructor
  · rintro (h0 | ⟨-, hz⟩ | ⟨a', X', hX', heq, hz⟩)
    · exact absurd (h0.symm ▸ none_mem_masterSig) none_not_mem_jU
    · exact hz
    · exact absurd (heq ▸ (show tu ∈ jU from rfl)) tu_not_mem_jc
  · intro hz; exact Or.inr (Or.inl ⟨rfl, hz⟩)

omit [Inhabited A] in

@[simp] theorem toCC_mem_jc {x : (Cn A).Element} {a : A} {X : Set (Strn A)} (hX : (Cn A).mem X) :
    (toCC x).mem (jc a X) ↔ x.mem (embA a X) := by
  constructor
  · rintro (h0 | ⟨heq, hz⟩ | ⟨a', X', hX', heqj, hz⟩)
    · exact absurd (h0 ▸ none_mem_masterSig) none_not_mem_jc
    · obtain ⟨t, ht⟩ := Cn_nonempty X hX
      exact absurd (heq ▸ (tc_mem_jc.mpr ht)) tc_not_mem_jU
    · obtain ⟨rfl, rfl⟩ := jc_eq_jc (Cn_nonempty X hX) heqj
      exact hz
  · intro hz; exact Or.inr (Or.inr ⟨a, X, hX, rfl, hz⟩)

omit [DecidableEq A] [Inhabited A] in
/-- Prefixed copies determine index and set: `aX = a'X'` (with `X` non-empty) forces `a=a'`, `X=X'`. -/
theorem embA_eq_embA {a a' : A} {X X' : Set (Strn A)} (hXne : X.Nonempty)
    (h : embA a X = embA a' X') : a = a' ∧ X = X' := by
  obtain ⟨w', hw'⟩ := hXne
  have hmem : (a :: w') ∈ embA a X := ⟨w', rfl, hw'⟩
  rw [h] at hmem
  obtain ⟨u, he, -⟩ := hmem
  rw [List.cons.injEq] at he; obtain ⟨rfl, -⟩ := he
  exact ⟨rfl, embA_injective h⟩

/-- **Inverse half of `Cₐ ≅ 𝟙 + Σ_a Cₐ`.** -/
def fromCC (s : (CCn A).Element) : (Cn A).Element where
  mem W := W = Set.univ
    ∨ (W = ({[]} : Set (Strn A)) ∧ s.mem jU)
    ∨ (∃ a X, (Cn A).mem X ∧ W = embA a X ∧ s.mem (jc a X))
  sub := by
    rintro W (rfl | ⟨rfl, -⟩ | ⟨a, X, hX, rfl, -⟩)
    · exact Or.inl ⟨[], coneN_nil.symm⟩
    · exact memCn_singleton []
    · exact memCn_embA a hX
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨rfl, hsU⟩ | ⟨a, X, hX, rfl, hsF⟩)
      (rfl | ⟨rfl, hsU'⟩ | ⟨a', X', hX', rfl, hsF'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr (Or.inl ⟨by rw [Set.univ_inter], hsU'⟩)
    · exact Or.inr (Or.inr ⟨a', X', hX', by rw [Set.univ_inter], hsF'⟩)
    · exact Or.inr (Or.inl ⟨by rw [Set.inter_univ], hsU⟩)
    · exact Or.inr (Or.inl ⟨by rw [Set.inter_self], hsU⟩)
    · exfalso
      have hs := s.inter_mem hsU hsF'; rw [jU_inter_jc] at hs
      obtain ⟨t, ht⟩ := sumSig_nonempty _ (s.sub hs); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr ⟨a, X, hX, by rw [Set.inter_univ], hsF⟩)
    · exfalso
      have hs := s.inter_mem hsF hsU'; rw [Set.inter_comm, jU_inter_jc] at hs
      obtain ⟨t, ht⟩ := sumSig_nonempty _ (s.sub hs); exact Set.notMem_empty t ht
    · by_cases haa : a = a'
      · subst haa
        have hs := s.inter_mem hsF hsF'; rw [jc_inter_jc_same] at hs
        exact Or.inr (Or.inr ⟨a, X ∩ X', sumSig_mem_jc_inv (s.sub hs), embA_inter a X X', hs⟩)
      · exfalso
        have hs := s.inter_mem hsF hsF'; rw [jc_inter_jc_ne haa] at hs
        obtain ⟨t, ht⟩ := sumSig_nonempty _ (s.sub hs); exact Set.notMem_empty t ht
  up_mem := by
    rintro W W' (rfl | ⟨rfl, hsU⟩ | ⟨a, X, hX, rfl, hsF⟩) hW' hsub
    · exact Or.inl (Set.univ_subset_iff.mp hsub)
    · rcases memCn_cases hW' with rfl | rfl | ⟨a', X', hX', rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨rfl, hsU⟩)
      · exact absurd (hsub (Set.mem_singleton_iff.mpr rfl)) nil_not_mem_embA
    · rcases memCn_cases hW' with rfl | rfl | ⟨a', X', hX', rfl⟩
      · exact Or.inl rfl
      · obtain ⟨t, ht⟩ := Cn_nonempty X hX
        have hm := hsub (⟨t, rfl, ht⟩ : (a :: t) ∈ embA a X)
        rw [Set.mem_singleton_iff] at hm; exact absurd hm (by simp)
      · obtain ⟨t, ht⟩ := Cn_nonempty X hX
        obtain ⟨w', he, -⟩ := hsub (⟨t, rfl, ht⟩ : (a :: t) ∈ embA a X)
        rw [List.cons.injEq] at he; obtain ⟨rfl, -⟩ := he
        refine Or.inr (Or.inr ⟨a, X', hX', rfl, ?_⟩)
        exact s.up_mem hsF (Or.inr (Or.inr ⟨a, X', hX', rfl⟩))
          (jc_subset_jc.mpr (embA_subset.mp hsub))

@[simp] theorem fromCC_mem_nil {s : (CCn A).Element} :
    (fromCC s).mem ({[]} : Set (Strn A)) ↔ s.mem (jU : Set (SigTok A (Strn A))) := by
  constructor
  · rintro (h0 | ⟨-, hs⟩ | ⟨a', X', hX', heq, hs⟩)
    · exact absurd h0 singleton_nil_ne_univ
    · exact hs
    · exact absurd heq (singleton_nil_ne_embA a' X')
  · intro hs; exact Or.inr (Or.inl ⟨rfl, hs⟩)

omit [Inhabited A] in

@[simp] theorem fromCC_mem_embA {s : (CCn A).Element} {a : A} {X : Set (Strn A)} (hX : (Cn A).mem X) :
    (fromCC s).mem (embA a X) ↔ s.mem (jc a X) := by
  constructor
  · rintro (h0 | ⟨heq, hs⟩ | ⟨a', X', hX', heqj, hs⟩)
    · exact absurd h0 (embA_ne_univ a X)
    · exact absurd heq.symm (singleton_nil_ne_embA a X)
    · obtain ⟨rfl, rfl⟩ := embA_eq_embA (Cn_nonempty X hX) heqj
      exact hs
  · intro hs; exact Or.inr (Or.inr ⟨a, X, hX, rfl, hs⟩)

omit [Inhabited A] in

theorem fromCC_toCC (x : (Cn A).Element) : fromCC (toCC x) = x := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨rfl, hs⟩ | ⟨a, X, hX, rfl, hs⟩)
    · exact x.master_mem
    · exact toCC_mem_jU.mp hs
    · exact (toCC_mem_jc hX).mp hs
  · intro hW
    rcases memCn_cases (x.sub hW) with rfl | rfl | ⟨a, X, hX, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨rfl, toCC_mem_jU.mpr hW⟩)
    · exact Or.inr (Or.inr ⟨a, X, hX, rfl, (toCC_mem_jc hX).mpr hW⟩)

theorem toCC_fromCC (s : (CCn A).Element) : toCC (fromCC s) = s := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨rfl, hs⟩ | ⟨a, X, hX, rfl, hs⟩)
    · exact s.master_mem
    · exact fromCC_mem_nil.mp hs
    · exact (fromCC_mem_embA hX).mp hs
  · intro hW
    rcases s.sub hW with rfl | rfl | ⟨a, X, hX, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨rfl, fromCC_mem_nil.mpr hW⟩)
    · exact Or.inr (Or.inr ⟨a, X, hX, rfl, (fromCC_mem_embA hX).mpr hW⟩)

/-- **The isomorphism `|Cₐ| ≃o |𝟙 + Σ_a Cₐ|`.** -/
def ccEquiv : (Cn A).Element ≃o (CCn A).Element where
  toFun := toCC
  invFun := fromCC
  left_inv := fromCC_toCC
  right_inv := toCC_fromCC
  map_rel_iff' := by
    intro x x'
    constructor
    · intro hle W hW
      rcases memCn_cases (x.sub hW) with rfl | rfl | ⟨a, X, hX, rfl⟩
      · exact x'.master_mem
      · exact toCC_mem_jU.mp (hle _ (Or.inr (Or.inl ⟨rfl, hW⟩)))
      · exact (toCC_mem_jc hX).mp (hle _ (Or.inr (Or.inr ⟨a, X, hX, rfl, hW⟩)))
    · intro hle W hW
      rcases hW with rfl | ⟨rfl, hz⟩ | ⟨a, X, hX, rfl, hz⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨rfl, hle _ hz⟩)
      · exact Or.inr (Or.inr ⟨a, X, hX, rfl, hle _ hz⟩)

@[simp] theorem ccEquiv_apply (x : (Cn A).Element) : ccEquiv x = toCC x := rfl

end Iso

section Algebra

variable {A : Type} [DecidableEq A] [Inhabited A]

/-- `Cₐ` as an object of the `∅`-free category. -/
abbrev Cnobj (A : Type) [DecidableEq A] : StrictDomainObj.{0} := ⟨Strn A, Cn A, Cn_nonempty⟩

@[simp] theorem Cnobj_sys (A : Type) [DecidableEq A] : (Cnobj A).sys = Cn A := rfl

/-- **The `Tsig`-algebra structure on `Cₐ`.** The structure map `i : 𝟙+Σ_a Cₐ → Cₐ` is the inverse of
the domain-equation isomorphism `ccEquiv`, strict by `isStrict_ofIso`. -/
abbrev cnStr : (((Tsig A).obj (Cnobj A)) ⟶ (Cnobj A)) :=
  ⟨ofIso ccEquiv.symm, isStrict_ofIso _⟩

/-- **`Cₐ` is a `Tsig`-algebra** for `Tsig(X) = 𝟙 + Σ_a X`. -/
abbrev Cnalg (A : Type) [DecidableEq A] [Inhabited A] : TAlgebra (Tsig A) := ⟨Cnobj A, cnStr⟩

end Algebra

section Iso

variable {A : Type} [DecidableEq A] [Inhabited A]

omit [Inhabited A] in

theorem consMapN_mem_embA {a : A} {z : (Cn A).Element} {X : Set (Strn A)} (hX : (Cn A).mem X) :
    ((consMapN a).toElementMap z).mem (embA a X) ↔ z.mem X := by
  constructor
  · rintro ⟨X', hzX', -, -, hsub⟩
    rw [← embA_eq_prependN] at hsub
    exact z.up_mem hzX' hX (embA_subset.mp hsub)
  · intro hz
    refine ⟨X, hz, z.sub hz, memCn_embA a hX, ?_⟩
    rw [← embA_eq_prependN]

omit [Inhabited A] in

theorem consMapN_not_mem_embA_ne {a c : A} (hac : a ≠ c) {z : (Cn A).Element} {X : Set (Strn A)} :
    ¬ ((consMapN a).toElementMap z).mem (embA c X) := by
  rintro ⟨X', hzX', hX'mem, -, hsub⟩
  obtain ⟨t, ht⟩ := Cn_nonempty X' hX'mem
  rw [← embA_eq_prependN] at hsub
  obtain ⟨w, hw, -⟩ := hsub ⟨t, rfl, ht⟩
  rw [List.cons.injEq] at hw; exact hac hw.1

omit [Inhabited A] in

theorem consMapN_not_mem_nil {a : A} {z : (Cn A).Element} :
    ¬ ((consMapN a).toElementMap z).mem ({[]} : Set (Strn A)) := by
  rintro ⟨X', hzX', hX'mem, -, hsub⟩
  obtain ⟨t, ht⟩ := Cn_nonempty X' hX'mem
  rw [← embA_eq_prependN] at hsub
  have hmem := hsub ⟨t, rfl, ht⟩
  rw [Set.mem_singleton_iff] at hmem; exact absurd hmem (by simp)

end Iso

section Initial

variable {A : Type} [DecidableEq A] [Inhabited A] (B : TAlgebra (Tsig A))

/-- The distinguished point `e = k(inj_𝟙)`: the image under `k` of the terminator. -/
def descE : B.carrier.sys.Element :=
  B.str.1.toElementMap (sinjU (h := B.carrier.nonempty))

/-- The `a`-th successor operation `f_a = k ∘ inj_a`. -/
def descF (a : A) (y : B.carrier.sys.Element) : B.carrier.sys.Element :=
  B.str.1.toElementMap (sinjC (h := B.carrier.nonempty) a y)

omit [Inhabited A] in

theorem descF_mono (a : A) {y y' : B.carrier.sys.Element} (h : y ≤ y') :
    descF B a y ≤ descF B a y' :=
  B.str.1.toElementMap_mono (sinjC_mono h)

/-- The recursion `φ(Λ)=z`, `φ(a·σ)=f_a(φ(σ))` on a finite string, with base value `z`. -/
def descVal (z : B.carrier.sys.Element) : Strn A → B.carrier.sys.Element
  | [] => z
  | a :: σ => descF B a (descVal z σ)

omit [Inhabited A] in

theorem descVal_append (z : B.carrier.sys.Element) (σ ρ : Strn A) :
    descVal B z (σ ++ ρ) = descVal B (descVal B z ρ) σ := by
  induction σ with
  | nil => rfl
  | cons a σ ih => exact congrArg (descF B a) ih

omit [Inhabited A] in

theorem descVal_mono_z {z z' : B.carrier.sys.Element} (h : z ≤ z') :
    ∀ σ, descVal B z σ ≤ descVal B z' σ
  | [] => h
  | _ :: σ => descF_mono B _ (descVal_mono_z h σ)

omit [Inhabited A] in

theorem descMap_hcone {σ τ : Strn A} (h : σ <+: τ) :
    descVal B B.carrier.sys.bot σ ≤ descVal B B.carrier.sys.bot τ := by
  obtain ⟨ρ, rfl⟩ := h
  rw [descVal_append]
  exact descVal_mono_z B (B.carrier.sys.bot_le _) σ

omit [Inhabited A] in

theorem descMap_hsing {σ τ : Strn A} (h : σ <+: τ) :
    descVal B B.carrier.sys.bot σ ≤ descVal B (descE B) τ := by
  obtain ⟨ρ, rfl⟩ := h
  rw [descVal_append]
  exact descVal_mono_z B (B.carrier.sys.bot_le _) σ

end Initial

section Lift

variable {A : Type} [DecidableEq A] [Inhabited A] {β : Type}

omit [Inhabited A] in
/-- Two maps out of `Cₐ` agree once they agree on every `σ⊥` and `σ` (generic `Exercise516.map_ext_C`). -/
theorem map_ext_Cn {V : NeighborhoodSystem β} {f g : ApproximableMap (Cn A) V}
    (hbot : ∀ σ, f.toElementMap (strBotN σ) = g.toElementMap (strBotN σ))
    (helem : ∀ σ, f.toElementMap (strElemN σ) = g.toElementMap (strElemN σ)) : f = g := by
  apply eq_of_toElementMap_principal
  intro X hX
  obtain (⟨σ, rfl⟩ | ⟨σ, rfl⟩) := (Cn_mem.mp hX)
  · exact hbot σ
  · exact helem σ

omit [DecidableEq A] in
/-- A cone is never contained in a singleton: it has the two distinct elements `τ` and `τ·default`. -/
theorem not_coneN_subset_singleton (τ σ : Strn A) : ¬ coneN τ ⊆ ({σ} : Set (Strn A)) := by
  intro h
  have h1 : τ ∈ ({σ} : Set (Strn A)) := h (show τ ∈ coneN τ from List.prefix_rfl)
  have h2 : (τ ++ [default]) ∈ ({σ} : Set (Strn A)) := h (List.prefix_append τ [default])
  rw [Set.mem_singleton_iff] at h1 h2
  have : τ = τ ++ [default] := h1.trans h2.symm
  simp at this

omit [DecidableEq A] in

theorem coneN_ne_singleton (τ σ : Strn A) : coneN τ ≠ ({σ} : Set (Strn A)) := fun h =>
  not_coneN_subset_singleton τ σ (h ▸ subset_rfl)

/-- A map `Cₐ → V` determined by its value `coneVal σ` on each partial element `σ⊥` and `singVal σ`
on each total element `σ`. (The alphabet-generic copy of `Exercise419.liftC`.) -/
def liftCn (V : NeighborhoodSystem β) (coneVal singVal : Strn A → V.Element)
    (hcone : ∀ {σ τ : Strn A}, σ <+: τ → coneVal σ ≤ coneVal τ)
    (hsing : ∀ {σ τ : Strn A}, σ <+: τ → coneVal σ ≤ singVal τ) :
    ApproximableMap (Cn A) V where
  rel X Y := (∃ σ, X = coneN σ ∧ (coneVal σ).mem Y) ∨ (∃ σ, X = {σ} ∧ (singVal σ).mem Y)
  rel_dom := by
    rintro X Y (⟨σ, rfl, _⟩ | ⟨σ, rfl, _⟩)
    · exact memCn_coneN σ
    · exact memCn_singleton σ
  rel_cod := by
    rintro X Y (⟨σ, _, hY⟩ | ⟨σ, _, hY⟩)
    · exact (coneVal σ).sub hY
    · exact (singVal σ).sub hY
  master_rel := by
    refine Or.inl ⟨[], ?_, (coneVal []).master_mem⟩
    rw [Cn_master]; exact coneN_nil.symm
  inter_right := by
    rintro X Y Y' (⟨σ, rfl, hY⟩ | ⟨σ, rfl, hY⟩) (⟨σ', hX', hY'⟩ | ⟨σ', hX', hY'⟩)
    · have hσσ : σ = σ' := coneN_injective hX'
      subst hσσ
      exact Or.inl ⟨σ, rfl, (coneVal σ).inter_mem hY hY'⟩
    · exact absurd hX' (coneN_ne_singleton σ σ')
    · exact absurd hX'.symm (coneN_ne_singleton σ' σ)
    · have hσσ : σ = σ' := by rw [Set.singleton_eq_singleton_iff] at hX'; exact hX'
      subst hσσ
      exact Or.inr ⟨σ, rfl, (singVal σ).inter_mem hY hY'⟩
  mono := by
    rintro X X' Y Y' (⟨σ, rfl, hY⟩ | ⟨σ, rfl, hY⟩) hX'X hYY' hX' hY'
    · rcases hX' with ⟨τ, rfl⟩ | ⟨τ, rfl⟩
      · have hpre : σ <+: τ := coneN_subset_coneN.mp hX'X
        exact Or.inl ⟨τ, rfl, (coneVal τ).up_mem (hcone hpre Y hY) hY' hYY'⟩
      · have hpre : σ <+: τ := singleton_subset_coneN.mp hX'X
        exact Or.inr ⟨τ, rfl, (singVal τ).up_mem (hsing hpre Y hY) hY' hYY'⟩
    · rcases hX' with ⟨τ, rfl⟩ | ⟨τ, rfl⟩
      · exact absurd hX'X (not_coneN_subset_singleton τ σ)
      · have hτσ : τ = σ := by
          have hmem := Set.singleton_subset_iff.mp hX'X
          rwa [Set.mem_singleton_iff] at hmem
        subst hτσ
        exact Or.inr ⟨τ, rfl, (singVal τ).up_mem hY hY' hYY'⟩

end Lift

section Initial

variable {A : Type} [DecidableEq A] [Inhabited A] (B : TAlgebra (Tsig A))

/-- **The homomorphism `Cₐ → E`**, built by `liftCn` from the head-recursion. -/
def descMap : ApproximableMap (Cn A) B.carrier.sys :=
  liftCn B.carrier.sys (descVal B B.carrier.sys.bot) (descVal B (descE B))
    (fun {_ _} => descMap_hcone B) (fun {_ _} => descMap_hsing B)

end Initial

section Lift

variable {A : Type} [DecidableEq A] [Inhabited A] {β : Type}

theorem liftCn_strBot (V : NeighborhoodSystem β) (coneVal singVal : Strn A → V.Element)
    (hcone : ∀ {σ τ : Strn A}, σ <+: τ → coneVal σ ≤ coneVal τ)
    (hsing : ∀ {σ τ : Strn A}, σ <+: τ → coneVal σ ≤ singVal τ) (σ : Strn A) :
    (liftCn V coneVal singVal hcone hsing).toElementMap (strBotN σ) = coneVal σ := by
  apply NeighborhoodSystem.Element.ext
  intro Y
  constructor
  · rintro ⟨X, ⟨_, hsub⟩, hrel⟩
    rcases hrel with ⟨σ', hXcone, hY⟩ | ⟨σ', hXsing, hY⟩
    · have hpre : σ' <+: σ := coneN_subset_coneN.mp (hXcone ▸ hsub)
      exact hcone hpre Y hY
    · exact absurd (hXsing ▸ hsub) (not_coneN_subset_singleton σ σ')
  · intro hY
    exact ⟨coneN σ, ⟨memCn_coneN σ, subset_rfl⟩, Or.inl ⟨σ, rfl, hY⟩⟩

end Lift

section Initial

variable {A : Type} [DecidableEq A] [Inhabited A] (B : TAlgebra (Tsig A))

@[simp] theorem descMap_strBot (σ : Strn A) :
    (descMap B).toElementMap (strBotN σ) = descVal B B.carrier.sys.bot σ :=
  liftCn_strBot _ _ _ _ _ σ

end Initial

section Lift

variable {A : Type} [DecidableEq A] [Inhabited A] {β : Type}

theorem liftCn_strElem (V : NeighborhoodSystem β) (coneVal singVal : Strn A → V.Element)
    (hcone : ∀ {σ τ : Strn A}, σ <+: τ → coneVal σ ≤ coneVal τ)
    (hsing : ∀ {σ τ : Strn A}, σ <+: τ → coneVal σ ≤ singVal τ) (σ : Strn A) :
    (liftCn V coneVal singVal hcone hsing).toElementMap (strElemN σ) = singVal σ := by
  apply NeighborhoodSystem.Element.ext
  intro Y
  constructor
  · rintro ⟨X, ⟨_, hsub⟩, hrel⟩
    rcases hrel with ⟨σ', hXcone, hY⟩ | ⟨σ', hXsing, hY⟩
    · have hpre : σ' <+: σ := by
        apply singleton_subset_coneN.mp; rw [← hXcone]; exact hsub
      exact hsing hpre Y hY
    · have hσσ' : σ = σ' := by
        have hmem := Set.singleton_subset_iff.mp (hXsing ▸ hsub)
        rwa [Set.mem_singleton_iff] at hmem
      subst hσσ'; exact hY
  · intro hY
    exact ⟨{σ}, ⟨memCn_singleton σ, subset_rfl⟩, Or.inr ⟨σ, rfl, hY⟩⟩

end Lift

section Initial

variable {A : Type} [DecidableEq A] [Inhabited A] (B : TAlgebra (Tsig A))

@[simp] theorem descMap_strElem (σ : Strn A) :
    (descMap B).toElementMap (strElemN σ) = descVal B (descE B) σ :=
  liftCn_strElem _ _ _ _ _ σ

omit [Inhabited A] in

theorem Cn_bot_eq_strBotN_nil : (Cn A).bot = strBotN ([] : Strn A) := by
  apply NeighborhoodSystem.Element.ext
  intro Y
  show ((Cn A).mem Y ∧ (Cn A).master ⊆ Y) ↔ ((Cn A).mem Y ∧ coneN [] ⊆ Y)
  rw [Cn_master, coneN_nil]

theorem ccEquiv_comp_symm :
    (ofIso (ccEquiv (A := A))).comp (ofIso ccEquiv.symm) = idMap (CCn A) := by
  apply ext_of_toElementMap
  intro s
  rw [toElementMap_comp, toElementMap_ofIso, toElementMap_ofIso, toElementMap_idMap]
  exact ccEquiv.apply_symm_apply s

theorem ccEquiv_symm_comp :
    (ofIso (ccEquiv (A := A)).symm).comp (ofIso ccEquiv) = idMap (Cn A) := by
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_comp, toElementMap_ofIso, toElementMap_ofIso, toElementMap_idMap]
  exact ccEquiv.symm_apply_apply x

theorem descMap_strict : IsStrict (descMap B) := by
  rw [isStrict_iff_apply_bot, Cn_bot_eq_strBotN_nil, descMap_strBot]
  rfl

/-- The bundled strict homomorphism `Cₐ → E`. -/
def descStrict : ((Cnobj A) ⟶ B.carrier) := ⟨descMap B, descMap_strict B⟩

theorem genKeyBot (g : ApproximableMap (Cn A) B.carrier.sys) :
    B.str.1.toElementMap ((sumMapSig (A := A) (h₀ := Cn_nonempty) (h₁ := B.carrier.nonempty)
        g).toElementMap (toCC (strBotN ([] : Strn A))))
      = B.carrier.sys.bot := by
  have hb : toCC (strBotN ([] : Strn A)) = (CCn A).bot := by
    rw [← Cn_bot_eq_strBotN_nil, ← ccEquiv_apply]; exact ccEquiv.map_bot
  rw [hb, isStrict_iff_apply_bot.mp (isStrict_sumMapSig (A := A) (h₀ := Cn_nonempty)
    (h₁ := B.carrier.nonempty) g)]
  exact isStrict_iff_apply_bot.mp B.str.2

end Initial

section Iso

variable {A : Type} [DecidableEq A] [Inhabited A]
omit [Inhabited A] in

/-- **`toCC ∘ (a·) = inj_a`.** Prepending the letter `a` to `z` is, across `Cₐ ≅ 𝟙+Σ_a Cₐ`, the
injection of `z` into the `a`-th summand. -/
theorem toCC_consMapN (a : A) (z : (Cn A).Element) :
    toCC ((consMapN a).toElementMap z) = sinjC (h := Cn_nonempty) a z := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨rfl, hz⟩ | ⟨c, X, hX, rfl, hz⟩)
    · exact Or.inl rfl
    · exact absurd hz consMapN_not_mem_nil
    · by_cases hac : a = c
      · subst hac; exact Or.inr ⟨X, hX, rfl, (consMapN_mem_embA hX).mp hz⟩
      · exact absurd hz (consMapN_not_mem_embA_ne hac)
  · rintro (rfl | ⟨X, hX, rfl, hm⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨a, X, hX, rfl, (consMapN_mem_embA hX).mpr hm⟩)

end Iso

section Initial

variable {A : Type} [DecidableEq A] [Inhabited A] (B : TAlgebra (Tsig A))

omit [Inhabited A] in

theorem genKey (g : ApproximableMap (Cn A) B.carrier.sys) (a : A) (w : (Cn A).Element) :
    B.str.1.toElementMap ((sumMapSig (A := A) (h₀ := Cn_nonempty) (h₁ := B.carrier.nonempty)
        g).toElementMap (toCC ((consMapN a).toElementMap w)))
      = descF B a (g.toElementMap w) := by
  rw [toCC_consMapN, sumMapSig_sinjC]; rfl

end Initial

section Iso

variable {A : Type} [DecidableEq A] [Inhabited A]
omit [Inhabited A] in

/-- **`toCC Λ̂ = inj_𝟙`.** The finished empty sequence is the terminator (the `𝟙`-summand). -/
theorem toCC_strElemN_nil :
    toCC (strElemN ([] : Strn A)) = sinjU (h := Cn_nonempty) := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨rfl, hz⟩ | ⟨a, X, hX, rfl, hz⟩)
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd (hz.2 (Set.mem_singleton_iff.mpr rfl)) nil_not_mem_embA
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨rfl, memCn_singleton [], subset_rfl⟩)

end Iso

section Initial

variable {A : Type} [DecidableEq A] [Inhabited A] (B : TAlgebra (Tsig A))

omit [Inhabited A] in

theorem genKey0 (g : ApproximableMap (Cn A) B.carrier.sys) :
    B.str.1.toElementMap ((sumMapSig (A := A) (h₀ := Cn_nonempty) (h₁ := B.carrier.nonempty)
        g).toElementMap (toCC (strElemN ([] : Strn A))))
      = descE B := by
  rw [toCC_strElemN_nil, sumMapSig_sinjU]; rfl

/-- `Cₐ`'s algebra map satisfies the recursion. -/
theorem descMap_satisfiesRec :
    descMap B = (B.str.1.comp (sumMapSig (A := A) (h₀ := Cn_nonempty) (h₁ := B.carrier.nonempty)
        (descMap B))).comp (ofIso ccEquiv) := by
  apply map_ext_Cn
  · intro σ
    rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, descMap_strBot]
    cases σ with
    | nil => exact (genKeyBot B (descMap B)).symm
    | cons a σ =>
      rw [ccEquiv_apply, ← consMapN_strBot]
      have h := genKey B (descMap B) a (strBotN σ)
      rw [descMap_strBot] at h
      exact h.symm
  · intro σ
    rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, descMap_strElem]
    cases σ with
    | nil => exact (genKey0 B (descMap B)).symm
    | cons a σ =>
      rw [ccEquiv_apply, ← consMapN_strElem]
      have h := genKey B (descMap B) a (strElemN σ)
      rw [descMap_strElem] at h
      exact h.symm

/-- **The homomorphism square** `desc ∘ i = k ∘ T(desc)`. -/
theorem descComm : (descMap B).comp (ofIso ccEquiv.symm)
    = B.str.1.comp (sumMapSig (A := A) (h₀ := Cn_nonempty) (h₁ := B.carrier.nonempty)
        (descMap B)) := by
  conv_lhs => rw [descMap_satisfiesRec B]
  rw [comp_assoc, ccEquiv_comp_symm, comp_idMap]

/-- **The descent homomorphism `(Cₐ, i) → (E, k)`** as a `Tsig`-algebra homomorphism. -/
def descAlgHom : AlgHom (Cnalg A) B where
  hom := descStrict B
  comm := by
    apply Subtype.ext
    simp only [StrictDomainObj.comp_val]
    exact descComm B

/-- **Any map satisfying the homomorphism recursion equals `descMap`.** -/
theorem rec_determines (g : ApproximableMap (Cn A) B.carrier.sys)
    (hg : g = (B.str.1.comp (sumMapSig (A := A) (h₀ := Cn_nonempty) (h₁ := B.carrier.nonempty)
        g)).comp (ofIso ccEquiv)) :
    g = descMap B := by
  have hbot : ∀ σ, g.toElementMap (strBotN σ) = descVal B B.carrier.sys.bot σ := by
    intro σ
    induction σ with
    | nil =>
      conv_lhs => rw [hg]
      rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, ccEquiv_apply]
      exact genKeyBot B g
    | cons a σ ih =>
      conv_lhs => rw [hg]
      rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, ccEquiv_apply,
        ← consMapN_strBot]
      have h := genKey B g a (strBotN σ)
      rw [ih] at h
      exact h
  have helem : ∀ σ, g.toElementMap (strElemN σ) = descVal B (descE B) σ := by
    intro σ
    induction σ with
    | nil =>
      conv_lhs => rw [hg]
      rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, ccEquiv_apply]
      exact genKey0 B g
    | cons a σ ih =>
      conv_lhs => rw [hg]
      rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, ccEquiv_apply,
        ← consMapN_strElem]
      have h := genKey B g a (strElemN σ)
      rw [ih] at h
      exact h
  apply map_ext_Cn
  · intro σ; rw [hbot, descMap_strBot]
  · intro σ; rw [helem, descMap_strElem]

/-- **Uniqueness.** Any `Tsig`-algebra homomorphism out of `(Cₐ, i)` equals `descAlgHom`. -/
theorem descAlgHom_uniq (h' : AlgHom (Cnalg A) B) : h' = descAlgHom B := by
  obtain ⟨hom, comm⟩ := h'
  have hg : hom.1 = descMap B := by
    refine rec_determines B hom.1 ?_
    have hc : hom.1.comp (ofIso ccEquiv.symm)
        = B.str.1.comp (sumMapSig (A := A) (h₀ := Cn_nonempty) (h₁ := B.carrier.nonempty) hom.1) := by
      exact congrArg Subtype.val comm
    have h2 := congrArg (fun m => m.comp (ofIso ccEquiv)) hc
    simp only at h2
    rw [comp_assoc] at h2
    erw [ccEquiv_symm_comp, comp_idMap] at h2
    exact h2
  have hhom : hom = descStrict B := Subtype.ext hg
  subst hhom
  rfl

end Initial

/-- **Exercise 6.17 part 2 — `(Cₐ, i)` is an initial `Tsig`-algebra for `Tsig(X) = 𝟙 + Σ_a X`.**
The descent map `φ : Cₐ → E` is the closed-form head-recursion `φ(Λ) = e`, `φ(a·x) = f_a(φ x)`
(`f_a = k ∘ inj_a`), built choice-free via `liftCn`; it is the unique `Tsig`-algebra homomorphism, so
`Cₐ` is the initial algebra of `X ↦ 𝟙 + Σ_a X`. -/
def CnisInitial (A : Type) [DecidableEq A] [Inhabited A] : IsInitial (Cnalg A) where
  desc := descAlgHom
  uniq := fun B h => descAlgHom_uniq B h

/-- **`Cₙ` is the initial algebra** of `X ↦ 𝟙 + Σ_{Fin (n+1)} X`. -/
def CfinIsInitial (n : ℕ) : IsInitial (Cnalg (Fin (n + 1))) := CnisInitial (Fin (n + 1))

/-- **Exercise 6.17 part 2 — the domain equation `Cₐ ≅ 𝟙 + Σ_a Cₐ`.** -/
theorem Cn_domain_equation (A : Type) [DecidableEq A] [Inhabited A] :
    Cn A ≅ᴰ CCn A := ⟨ccEquiv⟩

end

section
set_option linter.unusedVariables false

theorem example_617_gen : ∀ (A : Type) [inst : DecidableEq A] [Inhabited A],
  @DomainTheory.NeighbourhoodSystems.Isomorphic (DomainTheory.NeighbourhoodSystems.Exercise617Gen.Strn A)
    (DomainTheory.NeighbourhoodSystems.Exercise617Gen.SigTok A
      (DomainTheory.NeighbourhoodSystems.Exercise617Gen.Strn A))
    (@DomainTheory.NeighbourhoodSystems.Exercise617Gen.Cn A inst)
    (@DomainTheory.NeighbourhoodSystems.Exercise617Gen.CCn A inst) :=
  DomainTheory.NeighbourhoodSystems.Exercise617Gen.Cn_domain_equation
end

section
variable {A : Type} [DecidableEq A]

/-- **`Cₙ ≅ 𝟙 + (n+1)·Cₙ`** over the alphabet `Fin (n+1)`. -/
theorem Cfin_domain_equation (n : ℕ) : Cn (Fin (n + 1)) ≅ᴰ CCn (Fin (n + 1)) :=
  Cn_domain_equation (Fin (n + 1))
end

section
variable {A : Type}

section Iso

theorem embA_ne {a a' : A} (h : a ≠ a') {X Y : Set (Strn A)} (hX : X.Nonempty) :
    embA a X ≠ embA a' Y := by
  intro heq
  obtain ⟨w', hw'⟩ := hX
  have hmem : (a :: w') ∈ embA a' Y := heq ▸ (⟨w', rfl, hw'⟩ : (a :: w') ∈ embA a X)
  obtain ⟨w'', he, -⟩ := hmem
  rw [List.cons.injEq] at he; exact h he.1

end Iso

section Iso

theorem embA_nonempty {a : A} {X : Set (Strn A)} (hX : X.Nonempty) : (embA a X).Nonempty := by
  obtain ⟨w', hw'⟩ := hX; exact ⟨a :: w', w', rfl, hw'⟩

end Iso

end

end DomainTheory.NeighbourhoodSystems.Exercise617Gen
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

section
namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

/-- The "cons" of a head `a : |𝒟|` and a tail `b : |𝒟^∞|`, as a sequence `⟨a, b₀, b₁, …⟩`. -/
def consSeq (a : V.Element) (b : (iterSys V).Element) : ℕ → V.Element :=
  fun i => Nat.casesOn i a (fun k => component b k)

@[simp] theorem consSeq_zero (a : V.Element) (b : (iterSys V).Element) : consSeq a b 0 = a := rfl

@[simp] theorem consSeq_succ (a : V.Element) (b : (iterSys V).Element) (k : ℕ) :
    consSeq a b (k + 1) = component b k := rfl

/-- `⊥` of `𝒟^∞` is the all-`⊥` sequence. -/
theorem iterBot_eq : (iterSys V).bot = ofSeq (fun _ : ℕ => V.bot) := by
  apply Element.ext
  intro W
  rw [mem_bot, mem_ofSeq]
  constructor
  · rintro rfl
    refine ⟨(iterSys V).master_mem, fun i => ?_⟩
    rw [fiber_iterSys_master, mem_bot]
  · rintro ⟨_, hfib⟩
    apply eq_of_fiber_eq
    intro i
    have hi := hfib i
    rw [fiber_iterSys_master]
    rwa [mem_bot] at hi

/-- The `n`-th coordinate of `⊥` is `⊥`. -/
@[simp] theorem component_bot (n : ℕ) : component (iterSys V).bot n = V.bot := by
  rw [iterBot_eq, component_ofSeq]

/-- A successor-increasing chain is increasing. -/
theorem chain_le_of_succ {β : Type*} {W : NeighborhoodSystem β} {a : ℕ → W.Element}
    (h : ∀ n, a n ≤ a (n + 1)) {i j : ℕ} (hij : i ≤ j) : a i ≤ a j := by
  induction hij with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (h _)

section Target

variable {γ : Type*} {E : NeighborhoodSystem γ}

/-- The bottom map is below everything. -/
theorem constBot_le (f : ApproximableMap (iterSys V) E) :
    constMap (iterSys V) E.bot ≤ f := by
  intro X Y hrel
  obtain ⟨hX, hY⟩ := hrel
  rw [mem_bot] at hY; subst hY
  exact f.rel_master hX

end Target

/-- `i : 𝒟 × 𝒟^∞ → 𝒟^∞`, the "cons" iso (`iterProdIso⁻¹`); the `T`-algebra structure map. -/
def imap (V : NeighborhoodSystem α) : ApproximableMap (prod V (iterSys V)) (iterSys V) :=
  ofIso (iterProdIso V).symm

theorem isStrict_imap : IsStrict (imap V) := isStrict_ofIso _

/-- **The forward iso reads off head and tail.** `iterProdIso z = ⟨z₀, ⟨z₁,z₂,…⟩⟩`: the first
component is the `0`-coordinate `component z 0`, the second is the shifted sequence. -/
theorem iterProdIso_apply (z : (iterSys V).Element) :
    iterProdIso V z = pair (component z 0) (ofSeq (fun n => component z (n + 1))) := rfl

/-- **The inverse iso is "cons".** `iterProdIso⁻¹ ⟨a, b⟩ = ⟨a, b₀, b₁, …⟩`. -/
theorem iterProdIso_symm_pair (a : V.Element) (b : (iterSys V).Element) :
    (iterProdIso V).symm (pair a b) = ofSeq (consSeq a b) := by
  have hkey : iterProdIso V (ofSeq (consSeq a b)) = pair a b := by
    rw [iterProdIso_apply]
    congr 1
    · rw [component_ofSeq, consSeq_zero]
    · have : (fun n => component (ofSeq (consSeq a b)) (n + 1)) = fun n => component b n := by
        funext n; rw [component_ofSeq, consSeq_succ]
      rw [this, ofSeq_component]
  rw [← hkey, OrderIso.symm_apply_apply]

end Exercise618
end

section
namespace Exercise618

/-- The infinite iterate of an `∅`-free system is `∅`-free (each fibre is a non-empty neighbourhood). -/
theorem iterSys_nonempty {α : Type*} {V : NeighborhoodSystem α}
    (h : ∀ X, V.mem X → X.Nonempty) :
    ∀ W, (iterSys V).mem W → W.Nonempty := by
  rintro W ⟨hfib, _⟩
  obtain ⟨a, ha⟩ := h (fiber W 0) (hfib 0)
  exact ⟨(0, a), ha⟩

end Exercise618
end

section
namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

/-- `𝒟^∞` (Exercise 3.16's `iterSys`) as an `∅`-free object. -/
def iterObj (Dom : StrictDomainObj.{w}) : StrictDomainObj.{w} where
  carrier := ℕ × Dom.carrier
  sys := iterSys Dom.sys
  nonempty := iterSys_nonempty Dom.nonempty

/-- `j : 𝒟^∞ → 𝒟 × 𝒟^∞`, the splitting iso (`iterProdIso`). -/
def jmap (V : NeighborhoodSystem α) : ApproximableMap (iterSys V) (prod V (iterSys V)) :=
  ofIso (iterProdIso V)

section Target

variable {γ : Type*} {E : NeighborhoodSystem γ}

/-- The homomorphism operator `Op(f) = k ∘ T(f) ∘ j`. -/
def descOp (k : ApproximableMap (prod V E) E) (f : ApproximableMap (iterSys V) E) :
    ApproximableMap (iterSys V) E :=
  k.comp ((prodMap (idMap V) f).comp (jmap V))

/-- The defining action of the operator: `Op(f)(z) = k(z₀, f(⟨z₁,z₂,…⟩))`. -/
theorem descOp_apply (k : ApproximableMap (prod V E) E) (f : ApproximableMap (iterSys V) E)
    (z : (iterSys V).Element) :
    (descOp k f).toElementMap z
      = k.toElementMap (pair (component z 0)
          (f.toElementMap (ofSeq (fun n => component z (n + 1))))) := by
  simp only [descOp, jmap]
  rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, iterProdIso_apply,
    toElementMap_prodMap_pair, toElementMap_idMap]

/-- The descent chain `h₀ = ⊥`, `hₙ₊₁ = Op(hₙ)`. -/
def descSeq (k : ApproximableMap (prod V E) E) : ℕ → ApproximableMap (iterSys V) E
  | 0 => constMap (iterSys V) E.bot
  | (n + 1) => descOp k (descSeq k n)

end Target

section Uniq

variable {γ : Type*} {E : NeighborhoodSystem γ}

/-- **`g`-independence step.** If `g` is a homomorphism (`g ∘ i = k ∘ T(g)`) then
`g ∘ ρₙ₊₁ = k ∘ T(g ∘ ρₙ) ∘ j = Op_k(g ∘ ρₙ)`: the composite depends only on `g ∘ ρₙ`. -/
theorem gcomp_rho_succ (k : ApproximableMap (prod V E) E) (g : ApproximableMap (iterSys V) E)
    (hc : g.comp (imap V) = k.comp (prodMap (idMap V) g)) (n : ℕ) :
    g.comp (descSeq (imap V) (n + 1)) = descOp k (g.comp (descSeq (imap V) n)) := by
  show g.comp ((imap V).comp ((prodMap (idMap V) (descSeq (imap V) n)).comp (jmap V)))
     = k.comp ((prodMap (idMap V) (g.comp (descSeq (imap V) n))).comp (jmap V))
  rw [← comp_assoc, hc, comp_assoc]
  congr 1
  rw [← comp_assoc, ← prodMap_comp, idMap_comp]

/-- The descent chain for any strict `g` starts at the constant `⊥`: `g ∘ ρ₀ = ⊥`. -/
theorem gcomp_rho_zero (g : ApproximableMap (iterSys V) E) (hg : IsStrict g) :
    g.comp (descSeq (imap V) 0) = constMap (iterSys V) E.bot := by
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_comp, toElementMap_constMap,
    show descSeq (imap V) 0 = constMap (iterSys V) (iterSys V).bot from rfl,
    toElementMap_constMap, isStrict_iff_apply_bot.mp hg]

end Uniq

/-- `j ∘ i = I` on `𝒟 × 𝒟^∞`. -/
theorem jmap_comp_imap : (jmap V).comp (imap V) = idMap (prod V (iterSys V)) := by
  apply ext_of_toElementMap
  intro w
  simp only [jmap, imap]
  rw [toElementMap_comp, toElementMap_ofIso, toElementMap_ofIso, toElementMap_idMap,
    OrderIso.apply_symm_apply]

section Target

variable {γ : Type*} {E : NeighborhoodSystem γ}

/-- The continuity helper `k(a, ·) : E → E` as an approximable map. -/
def kHead (k : ApproximableMap (prod V E) E) (a : V.Element) :
    ApproximableMap E E :=
  k.comp (paired (constMap E a) (idMap E))

theorem kHead_apply (k : ApproximableMap (prod V E) E) (a : V.Element) (u : E.Element) :
    (kHead k a).toElementMap u = k.toElementMap (pair a u) := by
  rw [kHead, toElementMap_comp, toElementMap_paired, toElementMap_constMap, toElementMap_idMap]

end Target

/-- `⊥` of a product is the pair of `⊥`s. -/
theorem pair_bot {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} :
    pair V₀.bot V₁.bot = (prod V₀ V₁).bot := by
  apply Element.ext
  intro W
  rw [mem_bot, prod_master]
  constructor
  · rintro ⟨X, Y, hX, hY, rfl⟩
    rw [mem_bot] at hX hY; subst hX; subst hY; rfl
  · rintro rfl
    exact ⟨V₀.master, V₁.master, V₀.bot.master_mem, V₁.bot.master_mem, rfl⟩

section Target

variable {γ : Type*} {E : NeighborhoodSystem γ}

theorem descSeq_strict (k : ApproximableMap (prod V E) E) (hk : IsStrict k) :
    ∀ n, IsStrict (descSeq k n)
  | 0 => isStrict_constBot
  | (n + 1) => by
      have ih := descSeq_strict k hk n
      rw [isStrict_iff_apply_bot] at ih ⊢
      rw [show descSeq k (n + 1) = descOp k (descSeq k n) from rfl, descOp_apply]
      have htl : ofSeq (fun m => component (iterSys V).bot (m + 1)) = (iterSys V).bot := by
        have hconst : (fun m => component (iterSys V).bot (m + 1)) = (fun _ => V.bot) := by
          funext m; rw [component_bot]
        rw [hconst, ← iterBot_eq]
      rw [component_bot, htl, ih, pair_bot]
      exact isStrict_iff_apply_bot.mp hk

end Target

/-- `T(f₀ × f₁)` is strict when both factors are: `(f₀ × f₁)(⊥,⊥) = (f₀ ⊥, f₁ ⊥) = (⊥,⊥)`. -/
theorem isStrict_prodMap {α β α' β' : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
    {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}
    {f₀ : ApproximableMap V₀ V₀'} {f₁ : ApproximableMap V₁ V₁'}
    (hf₀ : IsStrict f₀) (hf₁ : IsStrict f₁) : IsStrict (prodMap f₀ f₁) := by
  rw [isStrict_iff_apply_bot, show (prod V₀ V₁).bot = pair V₀.bot V₁.bot from pair_bot.symm,
    toElementMap_prodMap_pair, isStrict_iff_apply_bot.mp hf₀, isStrict_iff_apply_bot.mp hf₁]
  exact pair_bot

end Exercise618
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Exercise618
section
set_option linter.unusedVariables false

theorem example_618.{u_2, u_3, u_4, u_5} : ∀ {α : Type u_2} {β : Type u_3} {α' : Type u_4} {β' : Type u_5}
  {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
  {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
  {V₀' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α'}
  {V₁' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β'}
  {f₀ : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α' V₀ V₀'}
  {f₁ : @DomainTheory.NeighbourhoodSystems.ApproximableMap β β' V₁ V₁'},
  @DomainTheory.NeighbourhoodSystems.Exercise510.IsStrict α α' V₀ V₀' f₀ →
    @DomainTheory.NeighbourhoodSystems.Exercise510.IsStrict β β' V₁ V₁' f₁ →
      @DomainTheory.NeighbourhoodSystems.Exercise510.IsStrict (Sum α β) (Sum α' β')
        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) (@DomainTheory.NeighbourhoodSystems.prod α' β' V₀' V₁')
        (@DomainTheory.NeighbourhoodSystems.prodMap α β α' β' V₀ V₁ V₀' V₁' f₀ f₁) :=
  @DomainTheory.NeighbourhoodSystems.Exercise618.isStrict_prodMap
end

end DomainTheory.NeighbourhoodSystems.Exercise618
namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

/-- `T(·) = (id_𝒟 × ·)` is monotone. -/
theorem prodMap_idMap_mono {γ : Type*} {E : NeighborhoodSystem γ}
    {f f' : ApproximableMap (iterSys V) E} (h : f ≤ f') :
    prodMap (idMap V) f ≤ prodMap (idMap V) f' := by
  intro W P hrel
  simp only [prodMap, paired_rel] at hrel ⊢
  exact ⟨hrel.1, hrel.2.1, comp_mono_gen h le_rfl _ _ hrel.2.2⟩

section Target

variable {γ : Type*} {E : NeighborhoodSystem γ}

theorem descOp_mono (k : ApproximableMap (prod V E) E) {f f' : ApproximableMap (iterSys V) E}
    (h : f ≤ f') : descOp k f ≤ descOp k f' :=
  comp_mono_gen le_rfl (comp_mono_gen (prodMap_idMap_mono h) le_rfl)

theorem descSeq_mono_succ (k : ApproximableMap (prod V E) E) (n : ℕ) :
    descSeq k n ≤ descSeq k (n + 1) := by
  induction n with
  | zero => exact constBot_le _
  | succ m ih => exact descOp_mono k ih

theorem descSeq_mono (k : ApproximableMap (prod V E) E) {n m : ℕ} (h : n ≤ m) :
    descSeq k n ≤ descSeq k m := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (descSeq_mono_succ k _)

theorem descSeq_dir (k : ApproximableMap (prod V E) E) :
    ∀ i j, ∃ l, (∀ X Y, (descSeq k i).rel X Y → (descSeq k l).rel X Y) ∧
      (∀ X Y, (descSeq k j).rel X Y → (descSeq k l).rel X Y) :=
  fun i j => ⟨max i j, fun _ _ => descSeq_mono k (le_max_left i j) _ _,
    fun _ _ => descSeq_mono k (le_max_right i j) _ _⟩

/-- **The descent map `h = ⋃ₙ hₙ : 𝒟^∞ → E`.** -/
def descMap (k : ApproximableMap (prod V E) E) : ApproximableMap (iterSys V) E :=
  iSupMap (descSeq k) (descSeq_dir k)

theorem descMap_toElementMap (k : ApproximableMap (prod V E) E) (z : (iterSys V).Element)
    {Y : Set γ} :
    ((descMap k).toElementMap z).mem Y ↔ ∃ n, ((descSeq k n).toElementMap z).mem Y :=
  mem_toElementMap_iSupMap (descSeq k) (descSeq_dir k) z

theorem descMap_strict (k : ApproximableMap (prod V E) E) (hk : IsStrict k) :
    IsStrict (descMap k) := by
  rw [isStrict_iff_apply_bot]
  apply Element.ext
  intro Y
  rw [mem_bot, descMap_toElementMap]
  constructor
  · rintro ⟨n, hn⟩
    have hs := descSeq_strict k hk n
    rw [isStrict_iff_apply_bot] at hs
    rw [hs, mem_bot] at hn
    exact hn
  · rintro rfl
    have hs := descSeq_strict k hk 0
    rw [isStrict_iff_apply_bot] at hs
    exact ⟨0, by rw [hs]; exact E.bot.master_mem⟩

end Target

end Exercise618
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise618

/-- The product of two `∅`-free systems is `∅`-free. -/
theorem prod_nonempty {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
    (h₀ : ∀ X, V₀.mem X → X.Nonempty) (_h₁ : ∀ Y, V₁.mem Y → Y.Nonempty) :
    ∀ W, (prod V₀ V₁).mem W → W.Nonempty := by
  rintro W ⟨X, Y, hX, _, rfl⟩
  obtain ⟨a, ha⟩ := h₀ X hX
  exact ⟨Sum.inl a, mem_prodNbhd_inl.mpr ha⟩

end Exercise618
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

/-- The fixed domain `𝒟` times an object `X`, again an `∅`-free domain. -/
def prodObj (Dom X : StrictDomainObj.{w}) : StrictDomainObj.{w} where
  carrier := Dom.carrier ⊕ X.carrier
  sys := prod Dom.sys X.sys
  nonempty := prod_nonempty Dom.nonempty X.nonempty

/-- The morphism action `T(f) = id_𝒟 × f`, strict by `isStrict_prodMap`. -/
def prodMapHom (Dom : StrictDomainObj.{w}) {X Y : StrictDomainObj.{w}} (f : (X ⟶ Y)) :
    ((prodObj Dom X) ⟶ (prodObj Dom Y)) :=
  ⟨prodMap (idMap Dom.sys) f.1, isStrict_prodMap isStrict_idMap f.2⟩

/-- **The product endofunctor `T(X) = 𝒟 × X`** on `∅`-free domains and strict maps, for a fixed
domain `𝒟`. On objects `T(X) = 𝒟 × X`; on maps `T(f) = id_𝒟 × f`. -/
def prodFunctor (Dom : StrictDomainObj.{w}) : Endofunctor StrictDomainObj.{w} where
  obj := prodObj Dom
  map := prodMapHom Dom
  map_id X := Subtype.ext (by
    show prodMap (idMap Dom.sys) (idMap X.sys) = idMap (prod Dom.sys X.sys)
    exact prodMap_id)
  map_comp {X Y Z} g f := Subtype.ext (by
    show prodMap (idMap Dom.sys) (g.1.comp f.1)
       = (prodMap (idMap Dom.sys) g.1).comp (prodMap (idMap Dom.sys) f.1)
    have h := prodMap_comp (idMap Dom.sys) (idMap Dom.sys) g.1 f.1
    rw [idMap_comp] at h
    exact h)

/-- **`𝒟^∞` as a `T`-algebra**, `(𝒟^∞, i)` with `i : 𝒟 × 𝒟^∞ → 𝒟^∞` the "cons" iso (`imap`,
Exercise 3.16's `iterProdIso⁻¹`), strict by `isStrict_imap`. -/
def iterAlg (Dom : StrictDomainObj.{w}) : TAlgebra (prodFunctor Dom) where
  carrier := iterObj Dom
  str := ⟨imap Dom.sys, isStrict_imap⟩

/-- **The truncation formula** `ρₙ(⟨x₀,x₁,…⟩) = ⟨x₀,…,x_{n-1},⊥,⊥,…⟩`. -/
theorem rho_apply (n : ℕ) (z : (iterSys V).Element) :
    (descSeq (imap V) n).toElementMap z
      = ofSeq (fun i => if i < n then component z i else V.bot) := by
  induction n generalizing z with
  | zero =>
    show (constMap (iterSys V) (iterSys V).bot).toElementMap z = _
    rw [toElementMap_constMap, iterBot_eq]
    congr 1
  | succ n ih =>
    rw [show descSeq (imap V) (n + 1) = descOp (imap V) (descSeq (imap V) n) from rfl,
      descOp_apply, ih]
    simp only [imap]
    rw [toElementMap_ofIso, iterProdIso_symm_pair]
    congr 1
    funext j
    cases j with
    | zero =>
      show component z 0 = if (0 : ℕ) < n + 1 then component z 0 else V.bot
      rw [ite_eq_left (Nat.zero_lt_succ n)]
    | succ k =>
      rw [consSeq_succ, component_ofSeq, component_ofSeq]
      show (if k < n then component z (k + 1) else V.bot)
         = if k + 1 < n + 1 then component z (k + 1) else V.bot
      by_cases h : k < n
      · rw [ite_eq_left h, ite_eq_left (Nat.succ_lt_succ h)]
      · rw [ite_eq_right h, ite_eq_right (fun hc => h (Nat.lt_of_succ_lt_succ hc))]

/-- **`⋃ₙ ρₙ = I`.** Every `z` is the directed union of its truncations: the cofinite-`Δ` structure
of `𝒟^∞` means each neighbourhood of `z` is already realised by a finite truncation. -/
theorem iSupRho_eq_id : descMap (imap V) = idMap (iterSys V) := by
  apply ext_of_toElementMap
  intro z
  rw [toElementMap_idMap]
  apply Element.ext
  intro Y
  rw [descMap_toElementMap]
  constructor
  · rintro ⟨n, hn⟩
    have hle : (descSeq (imap V) n).toElementMap z ≤ z := by
      rw [rho_apply]
      have hz : z = ofSeq (fun i => component z i) := (ofSeq_component z).symm
      conv_rhs => rw [hz]
      apply ofSeq_mono
      intro i
      show (if i < n then component z i else V.bot) ≤ component z i
      split
      · exact le_rfl
      · exact V.bot_le _
    exact hle Y hn
  · intro hzY
    have hY : (iterSys V).mem Y := z.sub hzY
    obtain ⟨N, hN⟩ := hY.2
    have hcomp : ∀ i, (component z i).mem (fiber Y i) := by
      have h := hzY
      rw [← ofSeq_component z] at h
      rw [mem_ofSeq] at h
      exact h.2
    refine ⟨N, ?_⟩
    rw [rho_apply, mem_ofSeq]
    refine ⟨hY, fun i => ?_⟩
    show (if i < N then component z i else V.bot).mem (fiber Y i)
    by_cases h : i < N
    · rw [ite_eq_left h]; exact hcomp i
    · rw [ite_eq_right h, hN i (not_lt.mp h)]; exact V.bot.master_mem

section Uniq

variable {γ : Type*} {E : NeighborhoodSystem γ}

/-- **Uniqueness.** Any two strict homomorphisms `g, g' : 𝒟^∞ → E` into a `T`-algebra `(E,k)` are
equal. By `g`-independence they agree on every truncation (`g ∘ ρₙ = g' ∘ ρₙ`), and `⋃ₙ ρₙ = I`
forces `g = g'`. -/
theorem comm_unique (k : ApproximableMap (prod V E) E)
    {g g' : ApproximableMap (iterSys V) E} (hg : IsStrict g) (hg' : IsStrict g')
    (hc : g.comp (imap V) = k.comp (prodMap (idMap V) g))
    (hc' : g'.comp (imap V) = k.comp (prodMap (idMap V) g')) : g = g' := by
  have hindep : ∀ n, g.comp (descSeq (imap V) n) = g'.comp (descSeq (imap V) n) := by
    intro n
    induction n with
    | zero => rw [gcomp_rho_zero g hg, gcomp_rho_zero g' hg']
    | succ m ih => rw [gcomp_rho_succ k g hc m, gcomp_rho_succ k g' hc' m, ih]
  have key : g.comp (descMap (imap V)) = g'.comp (descMap (imap V)) := by
    apply ApproximableMap.ext
    intro X Z
    simp only [descMap, comp_rel]
    constructor
    · rintro ⟨Y, ⟨i, hXY⟩, hYZ⟩
      have hg : (g.comp (descSeq (imap V) i)).rel X Z := ⟨Y, hXY, hYZ⟩
      rw [hindep i] at hg
      obtain ⟨Y', hXY', hYZ'⟩ := hg
      exact ⟨Y', ⟨i, hXY'⟩, hYZ'⟩
    · rintro ⟨Y, ⟨i, hXY⟩, hYZ⟩
      have hg' : (g'.comp (descSeq (imap V) i)).rel X Z := ⟨Y, hXY, hYZ⟩
      rw [← hindep i] at hg'
      obtain ⟨Y', hXY', hYZ'⟩ := hg'
      exact ⟨Y', ⟨i, hXY'⟩, hYZ'⟩
  rw [iSupRho_eq_id] at key
  rwa [comp_idMap, comp_idMap] at key

end Uniq

/-- Directedness of a successor-increasing chain. -/
theorem succChainDir {β : Type*} {W : NeighborhoodSystem β} (a : ℕ → W.Element)
    (h : ∀ n, a n ≤ a (n + 1)) : ∀ i j, ∃ l, a i ≤ a l ∧ a j ≤ a l :=
  fun i j => ⟨max i j, chain_le_of_succ h (le_max_left i j), chain_le_of_succ h (le_max_right i j)⟩

/-- Approximable maps are monotone in the map argument: `f ≤ g ⟹ f(x) ≤ g(x)`. -/
theorem toElementMap_le_of_le {β₀ β₁ : Type*} {W₀ : NeighborhoodSystem β₀}
    {W₁ : NeighborhoodSystem β₁} {f g : ApproximableMap W₀ W₁} (h : f ≤ g) (x : W₀.Element) :
    f.toElementMap x ≤ g.toElementMap x := by
  rintro Y ⟨X, hX, hrel⟩
  exact ⟨X, hX, h _ _ hrel⟩

section Target

variable {γ : Type*} {E : NeighborhoodSystem γ}

/-- The descent chain is increasing element-wise. -/
theorem descSeqEltMono (k : ApproximableMap (prod V E) E) (x : (iterSys V).Element) :
    ∀ n, (descSeq k n).toElementMap x ≤ (descSeq k (n + 1)).toElementMap x :=
  fun n => toElementMap_le_of_le (descSeq_mono_succ k n) x

/-- **The descent map as a directed union.** `h(x) = ⋃ₙ hₙ(x)`. -/
theorem descMap_eq (k : ApproximableMap (prod V E) E) (x : (iterSys V).Element) :
    (descMap k).toElementMap x
      = iSupDirected (fun n => (descSeq k n).toElementMap x)
          (succChainDir _ (descSeqEltMono k x)) := by
  apply Element.ext
  intro Y
  rw [descMap_toElementMap, mem_iSupDirected]

/-- **The descent map is a fixed point** of `Op = k ∘ T(·) ∘ j`. -/
theorem descMap_fix (k : ApproximableMap (prod V E) E) : descMap k = descOp k (descMap k) := by
  apply ext_of_toElementMap
  intro z
  rw [descOp_apply, descMap_eq k (ofSeq (fun n => component z (n + 1))),
    ← kHead_apply k (component z 0), toElementMap_iSupDirected, descMap_eq k z]
  -- both sides are directed unions; compare the (reindexed) families term-wise
  apply Element.ext
  intro Y
  rw [mem_iSupDirected, mem_iSupDirected]
  have hstep : ∀ m, (kHead k (component z 0)).toElementMap
        ((descSeq k m).toElementMap (ofSeq (fun n => component z (n + 1))))
      = (descSeq k (m + 1)).toElementMap z := by
    intro m
    rw [kHead_apply, show descSeq k (m + 1) = descOp k (descSeq k m) from rfl, descOp_apply]
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => exact ⟨0, by rw [hstep 0]; exact descSeqEltMono k z 0 _ hn⟩
    | succ m => exact ⟨m, by rw [hstep m]; exact hn⟩
  · rintro ⟨m, hm⟩
    rw [hstep m] at hm
    exact ⟨m + 1, hm⟩

/-- **Existence of the algebra homomorphism.** The descent map makes the square commute:
`descMap ∘ i = k ∘ T(descMap)` (using `j ∘ i = I` and the fixed-point equation). -/
theorem descMap_comm (k : ApproximableMap (prod V E) E) :
    (descMap k).comp (imap V) = k.comp (prodMap (idMap V) (descMap k)) := by
  conv_lhs => rw [descMap_fix k]
  show (k.comp ((prodMap (idMap V) (descMap k)).comp (jmap V))).comp (imap V)
     = k.comp (prodMap (idMap V) (descMap k))
  rw [comp_assoc, comp_assoc, jmap_comp_imap, comp_idMap]

end Target

/-- **The descent homomorphism `(𝒟^∞, i) → (E, k)`**: the strict map `descMap k` (existence half),
with the homomorphism square supplied by `descMap_comm`. -/
def descAlgHom (Dom : StrictDomainObj.{w}) (B : TAlgebra (prodFunctor Dom)) :
    AlgHom (iterAlg Dom) B where
  hom := ⟨descMap B.str.1, descMap_strict B.str.1 B.str.2⟩
  comm := by
    apply Subtype.ext
    show (descMap B.str.1).comp (imap Dom.sys)
       = B.str.1.comp (prodMap (idMap Dom.sys) (descMap B.str.1))
    exact descMap_comm B.str.1

end Exercise618
end
end DomainTheory.NeighbourhoodSystems
end

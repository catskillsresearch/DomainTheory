module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise_3_25
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise_1_23
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example_4_4
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise_4_19
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise_4_7
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem_4_1
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem_4_2
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_21
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise_5_10
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise_5_16
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem_5_6
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.Computability.MyhillNerode
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Set.Finite.Basic
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Definition_2_1
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Theorem_2_5
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_8
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_2
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_11
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_12
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Theorem_2_7
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_22
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise_6_27

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition_6_6
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510
section
universe w
namespace Theorem614
variable {α : Type w}
/- concordance: source L3861 THEOREM 6.14 existence of initial algebras -/
/-- **Theorem 6.14 (Scott 1981, PRG-19) — the canonical fixed point.** Under the hypotheses
(continuous on maps, monotone and continuous on domains, with a generating set `{Γ} ◁ T({Γ})`), the
iterated colimit `𝒟 = ⋃ₙ Tⁿ({Γ})` is a `T`-algebra whose structure map is an isomorphism
`T(𝒟) ≅ 𝒟` (the identity, since `T(𝒟) = 𝒟`), and there is a homomorphism from `𝒟` into every
`T`-algebra with a strict structure map (Theorem 6.9). This is Scott's *existence* of the initial
`T`-algebra. -/
theorem exists_algebra_with_hom (s : Setup.{w}) :
    ∃ A : TAlgebra s.T, Nonempty (Iso (s.T.obj A.carrier) A.carrier) ∧
      ∀ B : TAlgebra s.T, IsStrict B.str → Nonempty (AlgHom A B) :=
  ⟨colimAlg s, ⟨colimIso s⟩, fun B hk => nonempty_algHom s B hk⟩

end Theorem614
end

section
universe w

namespace Theorem614


variable {α : Type w}


/-- **`ρ₀ = ⊥`** when `{Γ}` is the trivial one-point system: `ρ₀` relates `X` only to the master.
This is where Scott's `{Γ}` (a *one-point* domain) is used. -/
theorem rho_zero_rel (s : Setup.{w}) (hΓ : ∀ X, s.Γ.mem X → X = s.Γ.master)
    {X Y : Set s.Tok} :
    (rho s 0).rel X Y ↔ (colim s).mem X ∧ Y = (colim s).master := by
  rw [rho_rel]
  constructor
  · rintro ⟨hcX, hcY, z, hz, _, hzY⟩
    have hzm : z = s.Γ.master := hΓ z hz
    subst hzm
    refine ⟨hcX, Set.Subset.antisymm ((colim s).sub_master hcY) ?_⟩
    rw [colim_master]; exact hzY
  · rintro ⟨hcX, rfl⟩
    refine ⟨hcX, (colim s).master_mem, s.Γ.master, s.Γ.master_mem, ?_, ?_⟩
    · have h := (colim s).sub_master hcX; rwa [colim_master] at h
    · rw [colim_master]

end Theorem614
end

section
universe w

namespace Theorem614


variable {α : Type w}


/-- For a strict map `g`, `g(⊥) = ⊥` relationally: `g` sends `Δ` only to `Δ`. -/
theorem strict_rel_master {β₀ β₁ : Type w} {V₀ : NeighborhoodSystem β₀}
    {V₁ : NeighborhoodSystem β₁} {g : ApproximableMap V₀ V₁} (hg : IsStrict g) {Z : Set β₁} :
    g.rel V₀.master Z ↔ Z = V₁.master :=
  ⟨fun h => hg h, fun h => h ▸ g.master_rel⟩

end Theorem614
end

section
universe w

namespace Theorem614


variable {α : Type w}


/-- For a strict homomorphism `g`, the base `g ∘ ρ₀` is the least map: it relates `X` only to the
master of `E`, independent of `g`. -/
theorem gcomp_rho_zero_rel (s : Setup.{w}) (hΓ : ∀ X, s.Γ.mem X → X = s.Γ.master)
    (B : TAlgebra s.T) {g : ApproximableMap (colim s) B.carrier.sys} (hg : IsStrict g)
    {X : Set s.Tok} {Z : Set B.carrier.carrier} :
    (g.comp (rho s 0)).rel X Z ↔ (colim s).mem X ∧ Z = B.carrier.sys.master := by
  rw [comp_rel]
  constructor
  · rintro ⟨Y, hrho, hgYZ⟩
    rw [rho_zero_rel s hΓ] at hrho
    obtain ⟨hcX, rfl⟩ := hrho
    exact ⟨hcX, (strict_rel_master hg).mp hgYZ⟩
  · rintro ⟨hcX, rfl⟩
    exact ⟨(colim s).master, (rho_zero_rel s hΓ).mpr ⟨hcX, rfl⟩, g.master_rel⟩

end Theorem614
end

section
universe w

namespace Theorem614


variable {α : Type w}


/-- The base case of `g`-independence: any two strict maps agree after `∘ ρ₀`. -/
theorem gcomp_rho_zero_indep (s : Setup.{w}) (hΓ : ∀ X, s.Γ.mem X → X = s.Γ.master)
    (B : TAlgebra s.T) {g g' : ApproximableMap (colim s) B.carrier.sys}
    (hg : IsStrict g) (hg' : IsStrict g') :
    g.comp (rho s 0) = g'.comp (rho s 0) := by
  apply ApproximableMap.ext
  intro X Z
  rw [gcomp_rho_zero_rel s hΓ B hg, gcomp_rho_zero_rel s hΓ B hg']

end Theorem614
end

section
universe w

namespace Theorem614


variable {α : Type w}


/-- Transport of a `Hom X X` along an object equality is heterogeneously equal to itself. -/
theorem transport_heq {Obj : Type*} [Category Obj] {X Y : Obj} (e : X = Y)
    (f : (X ⟶ X)) : HEq (e ▸ f : (Y ⟶ Y)) f := by
  cases e; rfl

end Theorem614
end

section
universe w

namespace Theorem614


variable {α : Type w}


/-- **`ρₙ₊₁ = i ∘ T(ρₙ) ∘ j`** (Scott's `T(ρₙ) = ρₙ₊₁`, conjugated by the structure iso). Since the
iso `𝒟 ≅ T(𝒟)` is the identity, this is the carrier transport of `T(ρₙ)`; combined with
`map_rho_heq` it pins `ρₙ₊₁`. -/
theorem key_rho (s : Setup.{w}) (n : ℕ) :
    rho s (n + 1) = (colimIso s).hom ⊚ Tmap_rho s n ⊚ (colimIso s).inv := by
  rw [show (colimIso s).hom = (isoOfEq (colimObj_eq s)).hom from rfl,
      show (colimIso s).inv = (isoOfEq (colimObj_eq s)).inv from rfl,
      isoOfEq_conj (colimObj_eq s) (Tmap_rho s n)]
  apply eq_of_heq
  exact HEq.trans (map_rho_heq s n).symm
    (transport_heq (colimObj_eq s) (Tmap_rho s n)).symm

end Theorem614
end

section
universe w

namespace Theorem614


variable {α : Type w}


/-- **The fixed-point recursion `gₙ₊₁ = k ∘ T(gₙ) ∘ j`.** Using `key_rho` (`ρₙ₊₁ = i∘T(ρₙ)∘j`) and the
homomorphism square `g ∘ i = k ∘ T(g)`. -/
theorem gcomp_rho_succ (s : Setup.{w}) (B : TAlgebra s.T) (g : AlgHom (colimAlg s) B) (n : ℕ) :
    g.hom.comp (rho s (n + 1))
      = B.str.comp ((s.T.map (X := objColim s) (Y := B.carrier)
          (g.hom.comp (rho s n))).comp (colimIso s).inv) := by
  have hcomm : g.hom ⊚ (colimIso s).hom
      = B.str ⊚ s.T.map (X := objColim s) (Y := B.carrier) g.hom := g.comm
  show g.hom ⊚ rho s (n + 1)
      = B.str ⊚ (s.T.map (X := objColim s) (Y := B.carrier) (g.hom ⊚ rho s n)) ⊚ (colimIso s).inv
  calc g.hom ⊚ rho s (n + 1)
      = g.hom ⊚ ((colimIso s).hom ⊚ (Tmap_rho s n ⊚ (colimIso s).inv)) :=
          congrArg (fun x => g.hom ⊚ x) (key_rho s n)
    _ = (g.hom ⊚ (colimIso s).hom) ⊚ (Tmap_rho s n ⊚ (colimIso s).inv) :=
          CategoryTheory.Category.assoc (Tmap_rho s n ⊚ (colimIso s).inv) (colimIso s).hom g.hom
    _ = (B.str ⊚ s.T.map (X := objColim s) (Y := B.carrier) g.hom)
            ⊚ (Tmap_rho s n ⊚ (colimIso s).inv) := by rw [hcomm]
    _ = B.str ⊚ (s.T.map (X := objColim s) (Y := B.carrier) g.hom
            ⊚ (Tmap_rho s n ⊚ (colimIso s).inv)) :=
          (CategoryTheory.Category.assoc (Tmap_rho s n ⊚ (colimIso s).inv)
            (s.T.map (X := objColim s) (Y := B.carrier) g.hom) B.str).symm
    _ = B.str ⊚ ((s.T.map (X := objColim s) (Y := B.carrier) g.hom ⊚ Tmap_rho s n)
            ⊚ (colimIso s).inv) :=
          congrArg (B.str ⊚ ·)
            (CategoryTheory.Category.assoc (colimIso s).inv (Tmap_rho s n)
              (s.T.map (X := objColim s) (Y := B.carrier) g.hom))
    _ = B.str ⊚ (s.T.map (X := objColim s) (Y := B.carrier) (g.hom ⊚ rho s n)
            ⊚ (colimIso s).inv) :=
          congrArg (fun m => B.str ⊚ (m ⊚ (colimIso s).inv))
            (s.T.map_comp (X := objColim s) (Y := objColim s) (Z := B.carrier) g.hom
              (rho s n)).symm

end Theorem614
end

section
universe w

namespace Theorem614


variable {α : Type w}


/-- **`g`-independence of `gₙ = g ∘ ρₙ`.** For any two strict homomorphisms into the same algebra,
`g ∘ ρₙ = g' ∘ ρₙ` for all `n` — the sequence is determined by the recursion, not by `g`. -/
theorem gcomp_rho_indep (s : Setup.{w}) (hΓ : ∀ X, s.Γ.mem X → X = s.Γ.master)
    (B : TAlgebra s.T) (g g' : AlgHom (colimAlg s) B)
    (hg : IsStrict g.hom) (hg' : IsStrict g'.hom) (n : ℕ) :
    g.hom.comp (rho s n) = g'.hom.comp (rho s n) := by
  induction n with
  | zero => exact gcomp_rho_zero_indep s hΓ B hg hg'
  | succ k ih => rw [gcomp_rho_succ s B g k, gcomp_rho_succ s B g' k, ih]

end Theorem614
end

section
universe w

namespace Theorem614


variable {α : Type w}


/-- **The underlying maps of two strict homomorphisms coincide**: `g = g ∘ I = g ∘ ⋃ₙ ρₙ =
⋃ₙ (g ∘ ρₙ)`, and the latter is `g`-independent. -/
theorem gcomp_eq (s : Setup.{w}) (hΓ : ∀ X, s.Γ.mem X → X = s.Γ.master)
    (B : TAlgebra s.T) (g g' : AlgHom (colimAlg s) B)
    (hg : IsStrict g.hom) (hg' : IsStrict g'.hom) :
    g.hom = g'.hom := by
  have key : g.hom.comp (iSupRho s) = g'.hom.comp (iSupRho s) := by
    apply ApproximableMap.ext
    intro X Z
    rw [comp_rel, comp_rel]
    constructor
    · rintro ⟨Y, ⟨n, hrho⟩, hgYZ⟩
      have hin : (g.hom.comp (rho s n)).rel X Z := ⟨Y, hrho, hgYZ⟩
      rw [gcomp_rho_indep s hΓ B g g' hg hg' n] at hin
      obtain ⟨Y', hrho', hgYZ'⟩ := hin
      exact ⟨Y', ⟨n, hrho'⟩, hgYZ'⟩
    · rintro ⟨Y, ⟨n, hrho⟩, hgYZ⟩
      have hin : (g'.hom.comp (rho s n)).rel X Z := ⟨Y, hrho, hgYZ⟩
      rw [← gcomp_rho_indep s hΓ B g g' hg hg' n] at hin
      obtain ⟨Y', hrho', hgYZ'⟩ := hin
      exact ⟨Y', ⟨n, hrho'⟩, hgYZ'⟩
  have e : g.hom.comp (idMap (colim s)) = g.hom := comp_idMap g.hom
  have e' : g'.hom.comp (idMap (colim s)) = g'.hom := comp_idMap g'.hom
  rw [← e, ← e', ← iSupRho_eq_id]
  exact key

end Theorem614
end

section
universe w

namespace Theorem614


variable {α : Type w}


/-- **Uniqueness of strict homomorphisms out of `𝒟`.** Any two strict `T`-algebra homomorphisms from
the canonical solution into the same algebra are equal. -/
theorem algHom_unique (s : Setup.{w}) (hΓ : ∀ X, s.Γ.mem X → X = s.Γ.master)
    (B : TAlgebra s.T) (g g' : AlgHom (colimAlg s) B)
    (hg : IsStrict g.hom) (hg' : IsStrict g'.hom) : g = g' :=
  algHom_ext (gcomp_eq s hΓ B g g' hg hg')

end Theorem614
end

section
universe w

namespace Theorem614


variable {α : Type w}


/-- **Theorem 6.14 (Scott 1981, PRG-19) — initial `T`-algebra.** When `{Γ}` is the one-point
generating system, the canonical solution `𝒟 = ⋃ₙ Tⁿ({Γ})` is the **initial** `T`-algebra among the
strict algebras: for every `T`-algebra `B` with a strict structure map there is a *unique* strict
homomorphism `𝒟 → B`. (Existence is Theorem 6.9; uniqueness is the `ρₙ` projection-chain argument.) -/
theorem exists_unique_strict_algHom (s : Setup.{w}) (hΓ : ∀ X, s.Γ.mem X → X = s.Γ.master)
    (B : TAlgebra s.T) (hk : IsStrict B.str) :
    ∃ g : AlgHom (colimAlg s) B, IsStrict g.hom ∧
      ∀ g' : AlgHom (colimAlg s) B, IsStrict g'.hom → g' = g := by
  obtain ⟨⟨g, hg⟩⟩ := nonempty_strict_algHom s B hk
  exact ⟨g, hg, fun g' hg' => algHom_unique s hΓ B g' g hg' hg⟩

end Theorem614
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Theorem614
section
set_option linter.unusedVariables false

theorem theorem_614.{w} : And
  (∀ (s : DomainTheory.NeighbourhoodSystems.Theorem614.Setup.{w}),
    ∃ (A :
      @DomainTheory.NeighbourhoodSystems.TAlgebra.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
        DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T),
      And
        (Nonempty.{w + 1}
          (@DomainTheory.NeighbourhoodSystems.Iso.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
            DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w}
            (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj.{w + 1, w}
              DomainTheory.NeighbourhoodSystems.DomainObj.{w}
              DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
              (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T A))
            (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
              DomainTheory.NeighbourhoodSystems.DomainObj.{w}
              DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T A)))
        (∀
          (B :
            @DomainTheory.NeighbourhoodSystems.TAlgebra.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
              DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T),
          @DomainTheory.NeighbourhoodSystems.Exercise510.IsStrict.{w, w}
              (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj.{w + 1, w}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                  (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                    DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                    DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B)).carrier
              (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B).carrier
              (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj.{w + 1, w}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                  (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                    DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                    DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B)).sys
              (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B).sys
              (@DomainTheory.NeighbourhoodSystems.TAlgebra.str.{w + 1, w}
                DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B) →
            Nonempty.{w + 1}
              (@DomainTheory.NeighbourhoodSystems.AlgHom.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T A B)))
  (∀ (s : DomainTheory.NeighbourhoodSystems.Theorem614.Setup.{w}),
    (∀ (X : Set.{w} s.Tok),
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem.{w} s.Tok s.Γ X →
          @Eq.{w + 1} (Set.{w} s.Tok) X (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master.{w} s.Tok s.Γ)) →
      ∀
        (B :
          @DomainTheory.NeighbourhoodSystems.TAlgebra.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
            DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T),
        @DomainTheory.NeighbourhoodSystems.Exercise510.IsStrict.{w, w}
            (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj.{w + 1, w}
                DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B)).carrier
            (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B).carrier
            (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj.{w + 1, w}
                DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B)).sys
            (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B).sys
            (@DomainTheory.NeighbourhoodSystems.TAlgebra.str.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
              DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B) →
          ∃ (g :
            @DomainTheory.NeighbourhoodSystems.AlgHom.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
              DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
              (DomainTheory.NeighbourhoodSystems.Theorem614.colimAlg.{w} s) B),
            And
              (@DomainTheory.NeighbourhoodSystems.Exercise510.IsStrict.{w, w}
                (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                    DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                    DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                    (DomainTheory.NeighbourhoodSystems.Theorem614.colimAlg.{w} s)).carrier
                (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                    DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                    DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B).carrier
                (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                    DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                    DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                    (DomainTheory.NeighbourhoodSystems.Theorem614.colimAlg.{w} s)).sys
                (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                    DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                    DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B).sys
                (@DomainTheory.NeighbourhoodSystems.AlgHom.hom.{w + 1, w}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                  (DomainTheory.NeighbourhoodSystems.Theorem614.colimAlg.{w} s) B g))
              (∀
                (g' :
                  @DomainTheory.NeighbourhoodSystems.AlgHom.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                    DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                    (DomainTheory.NeighbourhoodSystems.Theorem614.colimAlg.{w} s) B),
                @DomainTheory.NeighbourhoodSystems.Exercise510.IsStrict.{w, w}
                    (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                        DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                        DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                        (DomainTheory.NeighbourhoodSystems.Theorem614.colimAlg.{w} s)).carrier
                    (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                        DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                        DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B).carrier
                    (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                        DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                        DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                        (DomainTheory.NeighbourhoodSystems.Theorem614.colimAlg.{w} s)).sys
                    (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                        DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                        DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B).sys
                    (@DomainTheory.NeighbourhoodSystems.AlgHom.hom.{w + 1, w}
                      DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                      DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                      (DomainTheory.NeighbourhoodSystems.Theorem614.colimAlg.{w} s) B g') →
                  @Eq.{w + 1}
                    (@DomainTheory.NeighbourhoodSystems.AlgHom.{w + 1, w}
                      DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                      DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                      (DomainTheory.NeighbourhoodSystems.Theorem614.colimAlg.{w} s) B)
                    g' g)) :=
  @And.intro
  (∀ (s : DomainTheory.NeighbourhoodSystems.Theorem614.Setup.{w}),
    ∃ (A :
      @DomainTheory.NeighbourhoodSystems.TAlgebra.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
        DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T),
      And
        (Nonempty.{w + 1}
          (@DomainTheory.NeighbourhoodSystems.Iso.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
            DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w}
            (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj.{w + 1, w}
              DomainTheory.NeighbourhoodSystems.DomainObj.{w}
              DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
              (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T A))
            (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
              DomainTheory.NeighbourhoodSystems.DomainObj.{w}
              DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T A)))
        (∀
          (B :
            @DomainTheory.NeighbourhoodSystems.TAlgebra.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
              DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T),
          @DomainTheory.NeighbourhoodSystems.Exercise510.IsStrict.{w, w}
              (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj.{w + 1, w}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                  (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                    DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                    DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B)).carrier
              (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B).carrier
              (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj.{w + 1, w}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                  (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                    DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                    DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B)).sys
              (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B).sys
              (@DomainTheory.NeighbourhoodSystems.TAlgebra.str.{w + 1, w}
                DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B) →
            Nonempty.{w + 1}
              (@DomainTheory.NeighbourhoodSystems.AlgHom.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T A B)))
  (∀ (s : DomainTheory.NeighbourhoodSystems.Theorem614.Setup.{w}),
    (∀ (X : Set.{w} s.Tok),
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem.{w} s.Tok s.Γ X →
          @Eq.{w + 1} (Set.{w} s.Tok) X (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master.{w} s.Tok s.Γ)) →
      ∀
        (B :
          @DomainTheory.NeighbourhoodSystems.TAlgebra.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
            DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T),
        @DomainTheory.NeighbourhoodSystems.Exercise510.IsStrict.{w, w}
            (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj.{w + 1, w}
                DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B)).carrier
            (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B).carrier
            (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj.{w + 1, w}
                DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B)).sys
            (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B).sys
            (@DomainTheory.NeighbourhoodSystems.TAlgebra.str.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
              DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B) →
          ∃ (g :
            @DomainTheory.NeighbourhoodSystems.AlgHom.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
              DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
              (DomainTheory.NeighbourhoodSystems.Theorem614.colimAlg.{w} s) B),
            And
              (@DomainTheory.NeighbourhoodSystems.Exercise510.IsStrict.{w, w}
                (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                    DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                    DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                    (DomainTheory.NeighbourhoodSystems.Theorem614.colimAlg.{w} s)).carrier
                (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                    DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                    DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B).carrier
                (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                    DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                    DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                    (DomainTheory.NeighbourhoodSystems.Theorem614.colimAlg.{w} s)).sys
                (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                    DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                    DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B).sys
                (@DomainTheory.NeighbourhoodSystems.AlgHom.hom.{w + 1, w}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                  (DomainTheory.NeighbourhoodSystems.Theorem614.colimAlg.{w} s) B g))
              (∀
                (g' :
                  @DomainTheory.NeighbourhoodSystems.AlgHom.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                    DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                    (DomainTheory.NeighbourhoodSystems.Theorem614.colimAlg.{w} s) B),
                @DomainTheory.NeighbourhoodSystems.Exercise510.IsStrict.{w, w}
                    (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                        DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                        DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                        (DomainTheory.NeighbourhoodSystems.Theorem614.colimAlg.{w} s)).carrier
                    (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                        DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                        DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B).carrier
                    (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                        DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                        DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                        (DomainTheory.NeighbourhoodSystems.Theorem614.colimAlg.{w} s)).sys
                    (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                        DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                        DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B).sys
                    (@DomainTheory.NeighbourhoodSystems.AlgHom.hom.{w + 1, w}
                      DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                      DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                      (DomainTheory.NeighbourhoodSystems.Theorem614.colimAlg.{w} s) B g') →
                  @Eq.{w + 1}
                    (@DomainTheory.NeighbourhoodSystems.AlgHom.{w + 1, w}
                      DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                      DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                      (DomainTheory.NeighbourhoodSystems.Theorem614.colimAlg.{w} s) B)
                    g' g))
  DomainTheory.NeighbourhoodSystems.Theorem614.exists_algebra_with_hom.{w}
  DomainTheory.NeighbourhoodSystems.Theorem614.exists_unique_strict_algHom.{w}
end

end DomainTheory.NeighbourhoodSystems.Theorem614
namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

open Example62C in
/-- Every neighbourhood of the three-way separated sum `sum3` is non-empty (so `sum3` is again an
object of the `∅`-free category). -/
theorem sum3_nonempty {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
    {V₂ : NeighborhoodSystem γ} {h₀ : ∀ X, V₀.mem X → X.Nonempty}
    {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty} {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty} :
    ∀ W, (sum3 V₀ V₁ V₂ h₀ h₁ h₂).mem W → W.Nonempty := by
  rintro W (rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩ | ⟨Z, hZ, rfl⟩)
  · exact ⟨none, none_mem_master3⟩
  · exact j0_nonempty (h₀ X hX)
  · exact j1_nonempty (h₁ Y hY)
  · exact j2_nonempty (h₂ Z hZ)
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

section Equation

variable (D : NeighborhoodSystem α) (hD : ∀ X, D.mem X → X.Nonempty)

include hD

/-- The right-hand side of Scott's domain equation: the sum system `D + (D^§ × D^§)`. -/
def sumSys : NeighborhoodSystem (Option (α ⊕ ((List Bool × α) ⊕ (List Bool × α)))) :=
  sum D (prod (Dsharp D hD) (Dsharp D hD)) hD (prod_dsharp_nonempty D hD)

end Equation

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

section Equation

variable (D : NeighborhoodSystem α) (hD : ∀ X, D.mem X → X.Nonempty)

include hD

/-- No neighbourhood of the sum `D + (D^§ × D^§)` is empty. -/
theorem sumSys_mem_nonempty {W : Set (Option (α ⊕ ((List Bool × α) ⊕ (List Bool × α))))}
    (h : (sumSys D hD).mem W) : W.Nonempty := by
  rcases h with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
  · exact ⟨none, none_mem_sumMaster⟩
  · exact inj₀_nonempty (hD X hX)
  · exact inj₁_nonempty (prod_dsharp_nonempty D hD Y hY)

end Equation

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

section Equation

variable (D : NeighborhoodSystem α) (hD : ∀ X, D.mem X → X.Nonempty)

include hD

/-- A sum-neighbourhood of the form `0X` arises only from the left factor, so `X ∈ 𝒟`. -/
theorem sum_mem_inj₀_inv {X : Set α} (h : (sumSys D hD).mem (inj₀ X)) : D.mem X := by
  rcases h with h0 | ⟨X', hX', heq⟩ | ⟨Y', hY', heq⟩
  · exact absurd (h0 ▸ none_mem_sumMaster) none_mem_inj₀
  · rw [inj₀_injective heq]; exact hX'
  · obtain ⟨b, hb⟩ := prod_dsharp_nonempty D hD Y' hY'
    exact absurd (heq ▸ ir_mem_inj₁.mpr hb) ir_mem_inj₀

end Equation

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

section Equation

variable (D : NeighborhoodSystem α) (hD : ∀ X, D.mem X → X.Nonempty)

include hD

/-- A sum-neighbourhood of the form `1V` arises only from the right factor, so `V ∈ 𝒟^§ × 𝒟^§`. -/
theorem sum_mem_inj₁_inv {V : Set ((List Bool × α) ⊕ (List Bool × α))}
    (h : (sumSys D hD).mem (inj₁ V)) : (prod (Dsharp D hD) (Dsharp D hD)).mem V := by
  rcases h with h0 | ⟨X', hX', heq⟩ | ⟨Y', hY', heq⟩
  · exact absurd (h0 ▸ none_mem_sumMaster) none_mem_inj₁
  · obtain ⟨a, ha⟩ := hD X' hX'
    exact absurd (heq ▸ il_mem_inj₀.mpr ha) il_mem_inj₁
  · rw [inj₁_injective heq]; exact hY'

end Equation

end Example61
end

section
universe u
variable {Obj : Type u} [Category Obj] {T : Endofunctor Obj}

/-- For an algebra `A = (D, i)`, the functor turns the structure map into a new `T`-algebra
`(T(D), T(i))`. -/
abbrev tStr (A : TAlgebra T) : TAlgebra T where
  carrier := T.obj A.carrier
  str := T.map A.str
end

section
universe u
variable {Obj : Type u} [Category Obj] {T : Endofunctor Obj}

/-- The structure map `i : T(D) → D` is itself a homomorphism `(T(D), T(i)) → (D, i)`: the square
`i ∘ T(i) = i ∘ T(i)` commutes trivially. -/
def strHom (A : TAlgebra T) : AlgHom (tStr A) A where
  hom := A.str
  comm := rfl
end

section
universe u
variable {Obj : Type u} [Category Obj] {T : Endofunctor Obj}

/-- The composite `i ∘ j` of `i` with the descent homomorphism `j : (D,i) → (T(D),T(i))` is the
identity on `D`. -/
theorem str_comp_desc (A : TAlgebra T) (hA : IsInitial A) :
    A.str ⊚ (hA.desc (tStr A)).hom = (𝟙 A.carrier) := by
  have h : (strHom A).comp (hA.desc (tStr A)) = AlgHom.id A := by
    rw [hA.uniq A ((strHom A).comp (hA.desc (tStr A))), hA.uniq A (AlgHom.id A)]
  exact congrArg AlgHom.hom h
end

section
universe u
variable {Obj : Type u} [Category Obj] {T : Endofunctor Obj}

end

section
set_option linter.unusedVariables false

theorem theorem_67.{u, u_1} : ∀ {Obj : Type u} [inst : CategoryTheory.Category.{u_1, u} Obj]
  {T : @DomainTheory.NeighbourhoodSystems.Endofunctor Obj inst}
  (A : @DomainTheory.NeighbourhoodSystems.TAlgebra Obj inst T)
  (hA : @DomainTheory.NeighbourhoodSystems.IsInitial Obj inst T A),
  @Eq
    (@Quiver.Hom Obj (@CategoryTheory.CategoryStruct.toQuiver Obj (@CategoryTheory.Category.toCategoryStruct Obj inst))
      (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier Obj inst T A)
      (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier Obj inst T A))
    (@DomainTheory.NeighbourhoodSystems.compAfter Obj inst
      (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier Obj inst T A)
      (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj Obj inst T
        (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier Obj inst T A))
      (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier Obj inst T A)
      (@DomainTheory.NeighbourhoodSystems.TAlgebra.str Obj inst T A)
      (@DomainTheory.NeighbourhoodSystems.AlgHom.hom Obj inst T A (@DomainTheory.NeighbourhoodSystems.tStr Obj inst T A)
        (@DomainTheory.NeighbourhoodSystems.IsInitial.desc Obj inst T A hA
          (@DomainTheory.NeighbourhoodSystems.tStr Obj inst T A))))
    (@CategoryTheory.CategoryStruct.id Obj (@CategoryTheory.Category.toCategoryStruct Obj inst)
      (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier Obj inst T A)) :=
  @DomainTheory.NeighbourhoodSystems.str_comp_desc
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

/-- The strict map represented by `⊥` of the strict function space relates `X` to `Y` exactly when
`X` is a neighbourhood and `Y` is the master output: it is the constant-`⊥` (least) strict map. -/
theorem botStrict_rel {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
    {X : Set α} {Y : Set β} :
    (toStrictMap (strictFun V₀ V₁).bot).1.rel X Y ↔ V₀.mem X ∧ Y = V₁.master := by
  rw [toStrictMap_rel, NeighborhoodSystem.mem_bot, strictFun_master]
  constructor
  · intro h
    have hcb : (⟨constMap V₀ V₁.bot, isStrict_constBot⟩ : StrictMap V₀ V₁) ∈ sstep X Y := by
      rw [h]; exact Set.mem_univ _
    rw [mem_sstep, constMap_rel, NeighborhoodSystem.mem_bot] at hcb
    exact hcb
  · rintro ⟨hX, rfl⟩
    exact sstep_cod_master hX
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

/-- **The per-step computation of Theorem 6.9's operator.** For the operator `Op = (k ∘ · ∘ j) ∘ Φ`
on the strict function space, `Op(x)` is the strict map `k ∘ T(toStrictMap x) ∘ j`. This is the
content of `homOp_apply_filter` plus the defining property `hΦ` of the Definition 6.8 witness `Φ`. -/
theorem opStep (T : Endofunctor DomainObj.{w}) (D E : DomainObj.{w})
    (j : ApproximableMap D.sys (T.obj D).sys) (k : ApproximableMap (T.obj E).sys E.sys)
    (hj : IsStrict j) (hk : IsStrict k)
    (Φ : ApproximableMap (strictFun D.sys E.sys) (strictFun (T.obj D).sys (T.obj E).sys))
    (hΦ : ∀ f : StrictMap D.sys E.sys,
      (toStrictMap (Φ.toElementMap (toStrictFilter f))).1 = T.map (X := D) (Y := E) f.1)
    (x : (strictFun D.sys E.sys).Element) :
    (toStrictMap (((homOp T D E j k hj hk).comp Φ).toElementMap x)).1
      = k.comp ((T.map (X := D) (Y := E) (toStrictMap x).1).comp j) := by
  set h := toStrictMap x with hh
  have hx : toStrictFilter h = x := toStrictFilter_toStrictMap x
  have hφ : Φ.toElementMap x
      = toStrictFilter (toStrictMap (Φ.toElementMap (toStrictFilter h))) := by
    rw [← hx]; exact (toStrictFilter_toStrictMap _).symm
  rw [toElementMap_comp, hφ, homOp_apply_filter, toStrictMap_toStrictFilter]
  show k.comp ((toStrictMap (Φ.toElementMap (toStrictFilter h))).1.comp j)
      = k.comp ((T.map (X := D) (Y := E) h.1).comp j)
  rw [hΦ h]
end

section
universe u
variable {Obj : Type u} [Category Obj] {T : Endofunctor Obj}

end
end DomainTheory.NeighbourhoodSystems
end

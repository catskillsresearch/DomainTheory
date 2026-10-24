module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise_3_25
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise_1_23
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise_1_24
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Factoid_1_8
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Submonoid.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Definition_2_1
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Theorem_2_5
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_2
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example_2_3
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_11
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_8
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_9

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem_4_2
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem_4_1
public import Mathlib.Tactic.Monotonicity.Lemmas
public import Mathlib.Tactic.Bound

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap
section
variable {α : Type*} {V : NeighborhoodSystem α}
namespace ApproximableMap
/- concordance: source L2239 EXERCISE 4.10 domain above an element -/
/-- **Exercise 4.10 (Scott 1981, PRG-19).** The relativized neighbourhood system `Dₐ`: same tokens
and master, neighbourhoods exactly the members of the filter `a`. -/
def relSystem (a : V.Element) : NeighborhoodSystem α where
  mem X := a.mem X
  master := V.master
  master_nonempty := V.master_nonempty
  master_mem := a.master_mem
  sub_master := fun hX => V.sub_master (a.sub hX)
  inter_mem := fun hX hY _ _ => a.inter_mem hX hY

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

@[simp] theorem relSystem_mem (a : V.Element) {X : Set α} :
    (relSystem a).mem X ↔ a.mem X := Iff.rfl

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

@[simp] theorem relSystem_master (a : V.Element) : (relSystem a).master = V.master := rfl

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- The `𝒟`-element obtained from a `Dₐ`-filter by upward closure in `𝒟`. -/
def embed (a : V.Element) (g : (relSystem a).Element) : V.Element where
  mem X := V.mem X ∧ ∃ W, a.mem W ∧ g.mem W ∧ W ⊆ X
  sub := fun h => h.1
  master_mem := ⟨V.master_mem, V.master, a.master_mem, g.master_mem, subset_rfl⟩
  inter_mem := by
    rintro X Y ⟨hVX, Wx, haWx, hgWx, hWxX⟩ ⟨hVY, Wy, haWy, hgWy, hWyY⟩
    have haWxy : a.mem (Wx ∩ Wy) := a.inter_mem haWx haWy
    have hgWxy : g.mem (Wx ∩ Wy) := g.inter_mem hgWx hgWy
    have hsub : Wx ∩ Wy ⊆ X ∩ Y := Set.inter_subset_inter hWxX hWyY
    refine ⟨V.inter_mem hVX hVY (a.sub haWxy) hsub, Wx ∩ Wy, haWxy, hgWxy, hsub⟩
  up_mem := by
    rintro X Y ⟨hVX, W, haW, hgW, hWX⟩ hVY hXY
    exact ⟨hVY, W, haW, hgW, subset_trans hWX hXY⟩

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- `embed a g ⊑ a`: the embedding lands below `a`. -/
theorem embed_le (a : V.Element) (g : (relSystem a).Element) : embed a g ≤ a := by
  rintro X ⟨hVX, W, haW, _, hWX⟩
  exact a.up_mem haW hVX hWX

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

theorem embed_mono (a : V.Element) {g₁ g₂ : (relSystem a).Element} (h : g₁ ≤ g₂) :
    embed a g₁ ≤ embed a g₂ := by
  rintro X ⟨hVX, W, haW, hgW, hWX⟩
  exact ⟨hVX, W, haW, h _ hgW, hWX⟩

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

theorem le_of_embed_le (a : V.Element) {g₁ g₂ : (relSystem a).Element}
    (h : embed a g₁ ≤ embed a g₂) : g₁ ≤ g₂ := by
  intro X hg₁X
  have hVX : V.mem X := a.sub (g₁.sub hg₁X)
  have : (embed a g₂).mem X := h X ⟨hVX, X, g₁.sub hg₁X, hg₁X, subset_rfl⟩
  obtain ⟨_, W, haW, hg₂W, hWX⟩ := this
  exact g₂.up_mem hg₂W (g₁.sub hg₁X) hWX

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- **Exercise 4.10 (Scott 1981, PRG-19).** When `f(a) = a`, the restriction `f' : Dₐ → Dₐ`
(`f'(x) = f(x)`). The codomain condition uses `↑X ⊑ a ⟹ f(↑X) ⊑ f(a) = a`. -/
def relMap (f : ApproximableMap V V) {a : V.Element} (ha : f.toElementMap a = a) :
    ApproximableMap (relSystem a) (relSystem a) where
  rel X Y := a.mem X ∧ f.rel X Y
  rel_dom := fun h => h.1
  rel_cod := by
    rintro X Y ⟨haX, hXY⟩
    have hVX : V.mem X := a.sub haX
    have hpr : V.principal hVX ≤ a := fun Z ⟨hVZ, hXZ⟩ => a.up_mem haX hVZ hXZ
    have hmemfX : (f.toElementMap (V.principal hVX)).mem Y := (f.rel_iff_mem_principal hVX).mp hXY
    have hle : f.toElementMap (V.principal hVX) ≤ f.toElementMap a := f.toElementMap_mono hpr
    have : (f.toElementMap a).mem Y := hle Y hmemfX
    rw [ha] at this
    exact this
  master_rel := ⟨a.master_mem, f.master_rel⟩
  inter_right := by
    rintro X Y Y' ⟨haX, hXY⟩ ⟨_, hXY'⟩
    exact ⟨haX, f.inter_right hXY hXY'⟩
  mono := by
    rintro X X' Y Y' ⟨_, hXY⟩ hX'X hYY' haX' haY'
    exact ⟨haX', f.mono hXY hX'X hYY' (a.sub haX') (a.sub haY')⟩

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- The `Dₐ`-filter obtained from an element `x ⊑ a` by restriction (same membership). -/
def restrict (a : V.Element) (x : V.Element) (hx : x ≤ a) : (relSystem a).Element where
  mem X := x.mem X
  sub := fun h => hx _ h
  master_mem := x.master_mem
  inter_mem := fun hX hY => x.inter_mem hX hY
  up_mem := fun hX hY hXY => x.up_mem hX (a.sub hY) hXY

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

theorem embed_restrict (a : V.Element) (x : V.Element) (hx : x ≤ a) :
    embed a (restrict a x hx) = x := by
  apply Element.ext
  intro X
  constructor
  · rintro ⟨hVX, W, _, hxW, hWX⟩
    exact x.up_mem hxW hVX hWX
  · intro hxX
    exact ⟨x.sub hxX, X, hx _ hxX, hxX, subset_rfl⟩

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

theorem restrict_embed (a : V.Element) (g : (relSystem a).Element) :
    restrict a (embed a g) (embed_le a g) = g := by
  apply Element.ext
  intro X
  constructor
  · rintro ⟨hVX, W, haW, hgW, hWX⟩
    exact g.up_mem hgW (a.up_mem haW hVX hWX) hWX
  · intro hgX
    exact ⟨a.sub (g.sub hgX), X, g.sub hgX, hgX, subset_rfl⟩

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- **Exercise 4.10 (Scott 1981, PRG-19).** `|Dₐ| ≃o {x ∈ |𝒟| ∣ x ⊑ a}`: the relativized domain has
exactly the elements below `a` as its points, with the inherited order. -/
def relIso (a : V.Element) : (relSystem a).Element ≃o {x : V.Element // x ≤ a} where
  toFun g := ⟨embed a g, embed_le a g⟩
  invFun x := restrict a x.1 x.2
  left_inv g := restrict_embed a g
  right_inv x := Subtype.ext (embed_restrict a x.1 x.2)
  map_rel_iff' := by
    intro g₁ g₂
    constructor
    · intro h; exact le_of_embed_le a h
    · intro h; exact embed_mono a h

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap


/-- **Exercise 4.10 (Scott 1981, PRG-19).** Any fixed point of `f` below `fix(f)` *is* `fix(f)`:
a fixed point is a pre-fixed point, so leastness forces `fix(f) ⊑ x`. -/
theorem fixElement_below_unique (f : ApproximableMap V V) {x : V.Element}
    (hxle : x ≤ f.fixElement) (hxfix : f.toElementMap x = x) : x = f.fixElement := by
  have hge : f.fixElement ≤ x := fixElement_le_of_toElementMap_le f (le_of_eq hxfix)
  exact le_antisymm hxle hge

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap


/-- The restriction `f'` has the same action as `f`: `embed a (f'(g)) = f(embed a g)`. -/
theorem relMap_toElementMap_embed (f : ApproximableMap V V) {a : V.Element}
    (ha : f.toElementMap a = a) (g : (relSystem a).Element) :
    embed a ((relMap f ha).toElementMap g) = f.toElementMap (embed a g) := by
  apply Element.ext
  intro X
  constructor
  · rintro ⟨hVX, W, haW, ⟨U, hgU, haU, hUW⟩, hWX⟩
    -- `U ∈ g`, `U f W`, `W ⊆ X`; so `X ∈ f(embed g)` via the member `U` of `embed g`.
    refine ⟨U, ⟨a.sub haU, U, haU, hgU, subset_rfl⟩, ?_⟩
    exact f.mono hUW subset_rfl hWX (a.sub haU) hVX
  · rintro ⟨U, ⟨hVU, W, haW, hgW, hWU⟩, hUX⟩
    -- `W ∈ g`, `W ⊆ U`, `U f X`; so `W f X` and `X ∈ embed a (f'(g))`.
    have hVX : V.mem X := f.rel_cod hUX
    have hWX : f.rel W X := f.mono hUX hWU subset_rfl (a.sub haW) hVX
    have haX : a.mem X := by
      have hpr : V.principal (a.sub haW) ≤ a := fun Z ⟨hVZ, hXZ⟩ => a.up_mem haW hVZ hXZ
      have hmemfW : (f.toElementMap (V.principal (a.sub haW))).mem X :=
        (f.rel_iff_mem_principal (a.sub haW)).mp hWX
      have := (f.toElementMap_mono hpr) X hmemfW
      rw [ha] at this; exact this
    exact ⟨hVX, X, haX, ⟨W, hgW, haW, hWX⟩, subset_rfl⟩

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap


/-- **Exercise 4.10 (Scott 1981, PRG-19).** With `a = fix(f)`, the restricted map `f'` has *exactly
one* fixed point: the top element of `D_{fix f}`, namely `restrict (fix f)` of `fix f` itself. Every
`Dₐ`-fixed point `g` of `f'` satisfies `embed a g = fix f`, hence is this top element. -/
theorem relMap_unique_fixed (f : ApproximableMap V V)
    (ha : f.toElementMap f.fixElement = f.fixElement) (g : (relSystem f.fixElement).Element)
    (hg : (relMap f ha).toElementMap g = g) :
    g = restrict f.fixElement f.fixElement (le_refl _) := by
  -- `embed g` is a fixed point of `f` below `fix f`, hence equals `fix f`.
  have hembfix : f.toElementMap (embed f.fixElement g) = embed f.fixElement g := by
    rw [← relMap_toElementMap_embed f ha g, hg]
  have heq : embed f.fixElement g = f.fixElement :=
    fixElement_below_unique f (embed_le f.fixElement g) hembfix
  -- transport along the iso.
  have h1 : restrict f.fixElement (embed f.fixElement g) (embed_le f.fixElement g) = g :=
    restrict_embed f.fixElement g
  -- both restricts agree because their underlying elements agree.
  have h2 : restrict f.fixElement (embed f.fixElement g) (embed_le f.fixElement g)
      = restrict f.fixElement f.fixElement (le_refl _) := by
    apply Element.ext
    intro X
    show (embed f.fixElement g).mem X ↔ f.fixElement.mem X
    rw [heq]
  rw [← h1, h2]

end ApproximableMap
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.ApproximableMap
section
set_option linter.unusedVariables false

theorem example_410.{u_1} : And
  (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
    {x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V},
    @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
        x (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f) →
      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f x) x →
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) x
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f))
  (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
    (ha :
      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f))
    (g :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.relSystem α V
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f))),
    @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.relSystem α V
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f)))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.relSystem α V
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.relSystem α V
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.relMap α V f
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f) ha)
          g)
        g →
      @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.relSystem α V
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f)))
        g
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.restrict α V
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f)
          (@le_refl (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f)))) :=
  @And.intro
  (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
    {x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V},
    @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
        x (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f) →
      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f x) x →
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) x
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f))
  (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
    (ha :
      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f))
    (g :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.relSystem α V
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f))),
    @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.relSystem α V
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f)))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.relSystem α V
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.relSystem α V
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.relMap α V f
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f) ha)
          g)
        g →
      @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.relSystem α V
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f)))
        g
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.restrict α V
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f)
          (@le_refl (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f))))
  @DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement_below_unique
  @DomainTheory.NeighbourhoodSystems.ApproximableMap.relMap_unique_fixed
end

end DomainTheory.NeighbourhoodSystems.ApproximableMap
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- The inclusion `𝒟ₐ → 𝒟` as an approximable map: an `a`-neighbourhood `X` relates to any larger
`𝒟`-neighbourhood `Y ⊇ X`. Its elementwise action is `embed a` (`inclMap_toElementMap`). -/
def inclMap (a : V.Element) : ApproximableMap (relSystem a) V where
  rel X Y := a.mem X ∧ V.mem Y ∧ X ⊆ Y
  rel_dom := fun h => h.1
  rel_cod := fun h => h.2.1
  master_rel := ⟨a.master_mem, V.master_mem, subset_rfl⟩
  inter_right := by
    rintro X Y Y' ⟨haX, hVY, hXY⟩ ⟨_, hVY', hXY'⟩
    exact ⟨haX, V.inter_mem hVY hVY' (a.sub haX) (Set.subset_inter hXY hXY'),
      Set.subset_inter hXY hXY'⟩
  mono := by
    rintro X X' Y Y' ⟨_, _, hXY⟩ hX'X hYY' haX' hVY'
    exact ⟨haX', hVY', (hX'X.trans hXY).trans hYY'⟩

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap


/-- The inclusion's elementwise action is `embed a` (Exercise 4.10). -/
theorem inclMap_toElementMap (a : V.Element) (g : (relSystem a).Element) :
    (inclMap a).toElementMap g = embed a g := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X, hgX, haX, hVY, hXY⟩
    exact ⟨hVY, X, haX, hgX, hXY⟩
  · rintro ⟨hVY, W, haW, hgW, hWY⟩
    exact ⟨W, hgW, haW, hVY, hWY⟩

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap


/-- The inclusion is strict: `ι(⊥) = ⊥`. -/
theorem inclMap_bot (a : V.Element) : (inclMap a).toElementMap (relSystem a).bot = V.bot := by
  rw [inclMap_toElementMap]
  apply Element.ext
  intro Y
  rw [mem_bot]
  constructor
  · rintro ⟨hVY, W, _, hbW, hWY⟩
    rw [mem_bot] at hbW
    rw [hbW] at hWY
    exact Set.Subset.antisymm (V.sub_master hVY) hWY
  · rintro rfl
    exact ⟨V.master_mem, V.master, a.master_mem, (relSystem a).bot.master_mem, subset_rfl⟩

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap


/-- The inclusion intertwines `f'` with `f`: `ι ∘ f' = f ∘ ι` (from `relMap_toElementMap_embed`). -/
theorem inclMap_intertwine (f : ApproximableMap V V) {a : V.Element} (ha : f.toElementMap a = a)
    (g : (relSystem a).Element) :
    (inclMap a).toElementMap ((relMap f ha).toElementMap g) =
      f.toElementMap ((inclMap a).toElementMap g) := by
  rw [inclMap_toElementMap, inclMap_toElementMap, relMap_toElementMap_embed]

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}
open ApproximableMap
universe u

end
end DomainTheory.NeighbourhoodSystems
end

module
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise_3_14

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.DomainIso
@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem
variable {α β γ α' β' : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}
/- concordance: source L1436 EXERCISE 3.15 product isomorphisms -/
/-- **Exercise 3.15(i) (Scott 1981, PRG-19).** The commutativity order-isomorphism
`|𝒟₀ × 𝒟₁| ≃o |𝒟₁ × 𝒟₀|`, factored through Proposition 3.2 and the cartesian swap. -/
def prodCommD (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    (prod V₀ V₁).Element ≃o (prod V₁ V₀).Element :=
  (prodEquiv V₀ V₁).trans (OrderIso.prodComm.trans (prodEquiv V₁ V₀).symm)

/-- The product of two order isomorphisms, as an order isomorphism. -/
def prodCongrOrderIso {A B C D : Type*} [Preorder A] [Preorder B] [Preorder C] [Preorder D]
    (e₀ : A ≃o B) (e₁ : C ≃o D) : A × C ≃o B × D where
  toFun p := (e₀ p.1, e₁ p.2)
  invFun q := (e₀.symm q.1, e₁.symm q.2)
  left_inv p := by simp
  right_inv q := by simp
  map_rel_iff' := by
    rintro ⟨a, c⟩ ⟨a', c'⟩
    show (e₀ a, e₁ c) ≤ (e₀ a', e₁ c') ↔ (a, c) ≤ (a', c')
    rw [Prod.mk_le_mk, Prod.mk_le_mk, e₀.le_iff_le, e₁.le_iff_le]

/-- **Exercise 3.15(ii) (Scott 1981, PRG-19).** The associativity order-isomorphism
`|𝒟₀ × (𝒟₁ × 𝒟₂)| ≃o |(𝒟₀ × 𝒟₁) × 𝒟₂|`. -/
def prodAssocD (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ) :
    (prod V₀ (prod V₁ V₂)).Element ≃o (prod (prod V₀ V₁) V₂).Element :=
  (prodEquiv V₀ (prod V₁ V₂)).trans <|
    (prodCongrOrderIso (OrderIso.refl V₀.Element) (prodEquiv V₁ V₂)).trans <|
      (OrderIso.prodAssoc V₀.Element V₁.Element V₂.Element).symm.trans <|
        (prodCongrOrderIso (prodEquiv V₀ V₁).symm (OrderIso.refl V₂.Element)).trans
          (prodEquiv (prod V₀ V₁) V₂).symm

/-- For a `Unique` second factor, `A × C ≃o A` (forget the constant component). -/
def prodUniqueOrderIso (A C : Type*) [Preorder A] [Preorder C] [Unique C] : A × C ≃o A where
  toFun p := p.1
  invFun a := (a, default)
  left_inv p := by
    have : (default : C) = p.2 := Subsingleton.elim _ _
    simp [this]
  right_inv _ := rfl
  map_rel_iff' := by
    rintro ⟨a, c⟩ ⟨a', c'⟩
    simp only [Prod.mk_le_mk]
    exact ⟨fun h => ⟨h, le_of_eq (Subsingleton.elim c c')⟩, And.left⟩

/-- For a `Unique` first factor, `C × A ≃o A` (forget the constant component). -/
def uniqueProdOrderIso (A C : Type*) [Preorder A] [Preorder C] [Unique C] : C × A ≃o A where
  toFun p := p.2
  invFun a := (default, a)
  left_inv p := by
    have : (default : C) = p.1 := Subsingleton.elim _ _
    simp [this]
  right_inv _ := rfl
  map_rel_iff' := by
    rintro ⟨c, a⟩ ⟨c', a'⟩
    simp only [Prod.mk_le_mk]
    exact ⟨fun h => ⟨le_of_eq (Subsingleton.elim c c'), h⟩, And.right⟩

/-- The **terminal domain** `𝟙`: the neighbourhood system over `Unit` with the single
neighbourhood `Δ = univ`. Its domain `|𝟙|` has exactly one element (`⊥ = {Δ}`), so `𝟙` is the
*product of no factors*. -/
def unitSys : NeighborhoodSystem Unit where
  mem X := X = Set.univ
  master := Set.univ
  master_nonempty := ⟨(), Set.mem_univ _⟩
  master_mem := rfl
  inter_mem := by rintro X Y Z rfl rfl _ _; simp
  sub_master := by rintro X rfl; exact subset_rfl

/-- `|𝟙|` is a subsingleton: every element is `⊥`. -/
theorem unitSys_element_eq (x : unitSys.Element) : x = unitSys.bot := by
  apply Element.ext
  intro Y
  constructor
  · intro hY; rw [mem_bot]; exact x.sub hY
  · intro hY; rw [mem_bot] at hY; subst hY; exact x.master_mem

instance : Unique unitSys.Element where
  default := unitSys.bot
  uniq := unitSys_element_eq

/-- **Exercise 3.15(iii) (Scott 1981, PRG-19).** Two domain isomorphisms induce one on the products:
`|𝒟₀ × 𝒟₁| ≃o |𝒟₀' × 𝒟₁'|`. -/
def prodCongrD (e₀ : V₀.Element ≃o V₀'.Element) (e₁ : V₁.Element ≃o V₁'.Element) :
    (prod V₀ V₁).Element ≃o (prod V₀' V₁').Element :=
  (prodEquiv V₀ V₁).trans ((prodCongrOrderIso e₀ e₁).trans (prodEquiv V₀' V₁').symm)

/-- **Exercise 3.15 (empty product).** `𝟙` is a right unit: `𝒟 × 𝟙 ≅ 𝒟`. -/
def prodUnitD (V₀ : NeighborhoodSystem α) :
    (prod V₀ unitSys).Element ≃o V₀.Element :=
  (prodEquiv V₀ unitSys).trans (prodUniqueOrderIso _ _)

/-- **Exercise 3.15 (empty product).** `𝟙` is a left unit: `𝟙 × 𝒟 ≅ 𝒟`. -/
def unitProdD (V₀ : NeighborhoodSystem α) :
    (prod unitSys V₀).Element ≃o V₀.Element :=
  (prodEquiv unitSys V₀).trans (uniqueProdOrderIso _ _)

/-- **Exercise 3.15(iii).** `𝒟₀ ≅ 𝒟₀'` and `𝒟₁ ≅ 𝒟₁'` imply `𝒟₀ × 𝒟₁ ≅ 𝒟₀' × 𝒟₁'`. -/
theorem Isomorphic.prod (h₀ : V₀ ≅ᴰ V₀') (h₁ : V₁ ≅ᴰ V₁') : prod V₀ V₁ ≅ᴰ prod V₀' V₁' :=
  h₀.elim fun e₀ => h₁.elim fun e₁ => ⟨prodCongrD e₀ e₁⟩

/-- **Exercise 3.15(ii).** `𝒟₀ × (𝒟₁ × 𝒟₂) ≅ (𝒟₀ × 𝒟₁) × 𝒟₂`. -/
theorem prod_assoc_isomorphic : prod V₀ (prod V₁ V₂) ≅ᴰ prod (prod V₀ V₁) V₂ :=
  ⟨prodAssocD V₀ V₁ V₂⟩

/-- **Exercise 3.15(i).** `𝒟₀ × 𝒟₁ ≅ 𝒟₁ × 𝒟₀`. -/
theorem prod_comm_isomorphic : prod V₀ V₁ ≅ᴰ prod V₁ V₀ := ⟨prodCommD V₀ V₁⟩
end

section
set_option linter.unusedVariables false

theorem example_315.{u_1, u_2, u_4, u_5, u_3} : And
  (And
    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β},
      @DomainTheory.NeighbourhoodSystems.Isomorphic (Sum α β) (Sum β α)
        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) (@DomainTheory.NeighbourhoodSystems.prod β α V₁ V₀))
    (∀ {α : Type u_1} {β : Type u_2} {α' : Type u_4} {β' : Type u_5}
      {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {V₀' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α'}
      {V₁' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β'},
      @DomainTheory.NeighbourhoodSystems.Isomorphic α α' V₀ V₀' →
        @DomainTheory.NeighbourhoodSystems.Isomorphic β β' V₁ V₁' →
          @DomainTheory.NeighbourhoodSystems.Isomorphic (Sum α β) (Sum α' β')
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
            (@DomainTheory.NeighbourhoodSystems.prod α' β' V₀' V₁')))
  (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ},
    @DomainTheory.NeighbourhoodSystems.Isomorphic (Sum α (Sum β γ)) (Sum (Sum α β) γ)
      (@DomainTheory.NeighbourhoodSystems.prod α (Sum β γ) V₀ (@DomainTheory.NeighbourhoodSystems.prod β γ V₁ V₂))
      (@DomainTheory.NeighbourhoodSystems.prod (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)) :=
  @And.intro
  (And
    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β},
      @DomainTheory.NeighbourhoodSystems.Isomorphic (Sum α β) (Sum β α)
        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) (@DomainTheory.NeighbourhoodSystems.prod β α V₁ V₀))
    (∀ {α : Type u_1} {β : Type u_2} {α' : Type u_4} {β' : Type u_5}
      {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {V₀' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α'}
      {V₁' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β'},
      @DomainTheory.NeighbourhoodSystems.Isomorphic α α' V₀ V₀' →
        @DomainTheory.NeighbourhoodSystems.Isomorphic β β' V₁ V₁' →
          @DomainTheory.NeighbourhoodSystems.Isomorphic (Sum α β) (Sum α' β')
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
            (@DomainTheory.NeighbourhoodSystems.prod α' β' V₀' V₁')))
  (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ},
    @DomainTheory.NeighbourhoodSystems.Isomorphic (Sum α (Sum β γ)) (Sum (Sum α β) γ)
      (@DomainTheory.NeighbourhoodSystems.prod α (Sum β γ) V₀ (@DomainTheory.NeighbourhoodSystems.prod β γ V₁ V₂))
      (@DomainTheory.NeighbourhoodSystems.prod (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂))
  (@And.intro
    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β},
      @DomainTheory.NeighbourhoodSystems.Isomorphic (Sum α β) (Sum β α)
        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) (@DomainTheory.NeighbourhoodSystems.prod β α V₁ V₀))
    (∀ {α : Type u_1} {β : Type u_2} {α' : Type u_4} {β' : Type u_5}
      {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {V₀' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α'}
      {V₁' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β'},
      @DomainTheory.NeighbourhoodSystems.Isomorphic α α' V₀ V₀' →
        @DomainTheory.NeighbourhoodSystems.Isomorphic β β' V₁ V₁' →
          @DomainTheory.NeighbourhoodSystems.Isomorphic (Sum α β) (Sum α' β')
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) (@DomainTheory.NeighbourhoodSystems.prod α' β' V₀' V₁'))
    @DomainTheory.NeighbourhoodSystems.prod_comm_isomorphic @DomainTheory.NeighbourhoodSystems.Isomorphic.prod)
  @DomainTheory.NeighbourhoodSystems.prod_assoc_isomorphic
end

section
open NeighborhoodSystem
variable {α β γ α' β' : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}

theorem prod_unit_isomorphic : prod V₀ unitSys ≅ᴰ V₀ := ⟨prodUnitD V₀⟩

theorem unit_prod_isomorphic : prod unitSys V₀ ≅ᴰ V₀ := ⟨unitProdD V₀⟩
end
end DomainTheory.NeighbourhoodSystems
end

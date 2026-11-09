# Illustrative example

@import "BridgeTheorems_Illustrative_example.svg" {code_block=false}

**Landings** for the S-expression / tree domain (`SexSys` over `lowerBoundSystem`). These are the compared endpoints of the example; everything else in this section builds or unpacks them.

| Landing | Claim | Where |
| --- | --- | --- |
| `sexNeighborhoodIso` | `SexSys.Element ≃o` filters of basic opens (**1982 ≃o 1980**) | [Neighbourhood filters, ideals, and the identity](WorkedExampleSExpr/Basic.md) |
| `sexIdealIso` | `SexSys.Element ≃o Ideal(FiniteElement SexSys)` (**1982 ≃o algebraic / 1972 carrier**) | [same note](WorkedExampleSExpr/Basic.md) |
| `sexNeighborhoodIdealIso` | filters ≃o ideals (**1980 ≃o 1972 carrier**), closing the triangle | [same note](WorkedExampleSExpr/Basic.md) |
| `sexDomainEquationIso` | `SexSys.Element ≃o SexRhs.Element` (**`T ≃o A + (T × T)`**) | [The tree equation as an order isomorphism](WorkedExampleSExpr/sexDomainEquationIso.md) |
| `exists_sexNeighborhoodIso` | nonempty wrapper for the neighbourhood landing | [Existence of the neighbourhood-filter isomorphism](WorkedExampleSExpr/exists_sexNeighborhoodIso.md) |
| `exists_sexIdealIso` | nonempty wrapper for the ideal landing | [Existence of the ideal isomorphism](WorkedExampleSExpr/exists_sexIdealIso.md) |
| `exists_sexDomainEquationIso` | nonempty wrapper for the domain equation | [Existence of the tree-equation isomorphism](WorkedExampleSExpr/exists_sexDomainEquationIso.md) |

Secondary (not the compared fixed-point landing): `sexRhsSemanticIso` is the generic semantic factor `WithBot (|A| ⊕ (|T| × |T|)) ≃o |A + (T × T)|` in [The semantic factor of the separated sum](WorkedExampleSExpr/sexRhsSemanticIso.md).

- [The tree domain in three presentations](BridgeTheorems_Worked_example.md)
- [The lower-bound system of the natural numbers](WorkedExampleSExpr/lowerBoundSystem.md)
- [The tree information system](WorkedExampleSExpr/SexSys.md)
- [The sum-of-product information system](WorkedExampleSExpr/SexRhs.md)
- [Singleton atom elements](WorkedExampleSExpr/sexAtom.md)
- [The tree equation as an order isomorphism](WorkedExampleSExpr/sexDomainEquationIso.md)
- [The semantic factor of the separated sum](WorkedExampleSExpr/sexRhsSemanticIso.md)
- [Neighbourhood filters, ideals, and the identity on the tree domain](WorkedExampleSExpr/Basic.md)
- [The right-hand side is a separated sum of a product](WorkedExampleSExpr/sexRhs_eq_sum_product.md)
- [An atom belongs to its singleton closure](WorkedExampleSExpr/sexAtom_mem_self.md)
- [Unfolding an atom into the left summand](WorkedExampleSExpr/sexUnfold_atom.md)
- [Unfolding along the tree equation](WorkedExampleSExpr/sexDomainEquationIso_unfold.md)
- [Folding along the tree equation](WorkedExampleSExpr/sexDomainEquationIso_fold.md)
- [Existence of the tree-equation isomorphism](WorkedExampleSExpr/exists_sexDomainEquationIso.md)
- [Existence of the neighbourhood-filter isomorphism](WorkedExampleSExpr/exists_sexNeighborhoodIso.md)
- [Existence of the ideal isomorphism](WorkedExampleSExpr/exists_sexIdealIso.md)
- [The identity map on tree elements](WorkedExampleSExpr/sexId_toElement.md)

<p style="color:#15803d;margin-top:1em;">✓ <strong>Revised</strong> (2026-11-09) — <a href="../BridgeTheorems_REVISION.md">Bridge revision progress</a></p>

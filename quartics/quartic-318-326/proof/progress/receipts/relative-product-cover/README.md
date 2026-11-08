# Actual relative input-product cover

This packet constructs the actual four-chart open cover of the completed curve's relative fiber product. `GenericProductCover318.cover` takes the relative product of arbitrary Scheme open covers. Its projection identities are proved. `WeierstrassTwoChartCover318.cover` is the literal finite/infinity two-chart cover; `productCover` is its actual relative product cover. `SchemeAffineTestExt318.hom_ext` proves that equality on all affine test schemes is enough for Scheme morphism equality, retaining nonreduced coefficient directions.

The packet does not define global multiplication or establish group axioms. Existing addition morphisms still need to be transported to this cover and proved compatible on the entire intersections.

Run `bash run.sh`; it holds the shared exclusive compile lock, replays each source with full kernel checking, and recursively audits all declarations. The only allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`.

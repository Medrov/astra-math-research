import AlgebraObject
import GraphObject

namespace Bridge

/-- Exact equality of two energy descriptions, only in this rational model. -/
theorem energy_correspondence (d f : Fin 3 → ℚ) :
    AlgebraObject.energy d f = GraphObject.energy d f := by
  exact MathResearch.AlbertSpectralGeometry.associatorDirichlet_graphLaplacian d f

end Bridge

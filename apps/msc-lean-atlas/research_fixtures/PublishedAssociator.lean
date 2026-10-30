import MathResearch.AlbertSpectralGeometry
-- atlas-project-library-sha256: 7c5615080ca86b60f1cab70de957cef066457d93b57d7df783b9c7e0d97ceef9

/- Named adapters from examples/astra_energy. The imported published model is
freshly compiled from its source closure by the local research verifier. -/
namespace AlgebraObject
open MathResearch.AlbertSpectralGeometry

def energy (d f : Fin 3 → ℚ) : ℚ := associatorDirichlet d f

end AlgebraObject

namespace GraphObject
open MathResearch.AlbertSpectralGeometry

def energy (d f : Fin 3 → ℚ) : ℚ :=
  f 0 * graphLaplacian d f 0 + f 1 * graphLaplacian d f 1 +
    f 2 * graphLaplacian d f 2

end GraphObject

namespace Bridge

/-- Reuse of the published energy identity in its exact rational model. -/
theorem energy_correspondence (d f : Fin 3 → ℚ) :
    AlgebraObject.energy d f = GraphObject.energy d f := by
  exact MathResearch.AlbertSpectralGeometry.associatorDirichlet_graphLaplacian d f

end Bridge

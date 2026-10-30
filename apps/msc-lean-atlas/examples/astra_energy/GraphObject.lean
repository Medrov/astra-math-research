import MathResearch.AlbertSpectralGeometry

/- Weighted graph energy on three vertices. The weights are provided by the
   already published model; no arbitrary graph equivalence is claimed. -/
namespace GraphObject
open MathResearch.AlbertSpectralGeometry

def energy (d f : Fin 3 → ℚ) : ℚ :=
  f 0 * graphLaplacian d f 0 + f 1 * graphLaplacian d f 1 +
    f 2 * graphLaplacian d f 2
end GraphObject

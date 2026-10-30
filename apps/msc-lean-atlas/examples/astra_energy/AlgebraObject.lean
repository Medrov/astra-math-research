import MathResearch.AlbertSpectralGeometry

/- A named input object from the published rational algebra model.
   This is an adapter to an existing definition, not a new discovery. -/
namespace AlgebraObject
open MathResearch.AlbertSpectralGeometry

def energy (d f : Fin 3 → ℚ) : ℚ := associatorDirichlet d f
end AlgebraObject

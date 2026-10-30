param(
    [ValidateRange(1, 65535)]
    [int]$Port = 8765
)

$ErrorActionPreference = 'Stop'
$atlasPython = Join-Path $PSScriptRoot '.venv\Scripts\python.exe'
if (-not (Test-Path -LiteralPath $atlasPython)) {
    throw 'Create .venv with python -m venv .venv, then run .venv\Scripts\python.exe -m pip install -r requirements-research.lock.'
}

$previousUtf8 = $env:PYTHONUTF8
$previousPath = $env:PATH
$previousLean = $env:ATLAS_LEAN
$atlasElanBin = Join-Path $env:USERPROFILE '.elan\bin'
try {
    # Keep Russian text and Lean Unicode intact in this process and its children.
    $env:PYTHONUTF8 = '1'
    if (Test-Path -LiteralPath $atlasElanBin) {
        $env:PATH = "$atlasElanBin;$env:PATH"
    }
    Push-Location $PSScriptRoot
    try {
        # Compilers run in temporary folders without lean-toolchain. Resolve
        # elan's project-selected compiler before leaving the repository.
        if (-not $env:ATLAS_LEAN -and (Get-Command elan -ErrorAction SilentlyContinue)) {
            $atlasLean = & elan which lean 2>$null
            if ($LASTEXITCODE -eq 0 -and (Test-Path -LiteralPath $atlasLean)) {
                $env:ATLAS_LEAN = $atlasLean
            }
        }
        & $atlasPython -X utf8 (Join-Path $PSScriptRoot 'server.py') --port $Port
        $atlasExitCode = $LASTEXITCODE
    }
    finally {
        Pop-Location
    }
}
finally {
    $env:PYTHONUTF8 = $previousUtf8
    $env:PATH = $previousPath
    $env:ATLAS_LEAN = $previousLean
}
exit $atlasExitCode

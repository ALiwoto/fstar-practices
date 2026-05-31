[CmdletBinding()]
param(
    [string[]] $ProofRoots = @("basic_proofs", "kaprekar_proofs"),
    [string[]] $FStarArgs = @(),
    [switch] $FailFast
)

$ErrorActionPreference = "Stop"

if ($PSScriptRoot) {
    $RepoRoot = Resolve-Path (Join-Path $PSScriptRoot "..")
} else {
    $RepoRoot = Resolve-Path "."
}

function ConvertTo-RepoRelativePath {
    param(
        [Parameter(Mandatory = $true)]
        [string] $Path
    )

    $absolutePath = [System.IO.Path]::GetFullPath($Path)
    $rootPath = [System.IO.Path]::GetFullPath($RepoRoot.Path)

    if (-not $rootPath.EndsWith([System.IO.Path]::DirectorySeparatorChar)) {
        $rootPath += [System.IO.Path]::DirectorySeparatorChar
    }

    $rootUri = [System.Uri]::new($rootPath)
    $pathUri = [System.Uri]::new($absolutePath)
    return [System.Uri]::UnescapeDataString(
        $rootUri.MakeRelativeUri($pathUri).ToString()
    ).Replace("/", [System.IO.Path]::DirectorySeparatorChar)
}

$proofFiles = foreach ($root in $ProofRoots) {
    $rootPath = Join-Path $RepoRoot $root

    if (-not (Test-Path -LiteralPath $rootPath -PathType Container)) {
        Write-Warning "Proof root not found: $root"
        continue
    }

    Get-ChildItem -LiteralPath $rootPath -File -Recurse |
        Where-Object { $_.Extension -in @(".fst", ".fsti") }
}

$proofFiles = @($proofFiles | Sort-Object FullName)

if ($proofFiles.Count -eq 0) {
    Write-Error "No .fst or .fsti proof files found under: $($ProofRoots -join ', ')"
    exit 1
}

Push-Location $RepoRoot
try {
    $failed = New-Object System.Collections.Generic.List[object]
    $passed = 0
    $index = 0

    foreach ($file in $proofFiles) {
        $index += 1
        $relativePath = ConvertTo-RepoRelativePath $file.FullName
        Write-Host "[$index/$($proofFiles.Count)] Verifying $relativePath"

        $commandArgs = @($FStarArgs) + @($relativePath)
        $stdoutFile = New-TemporaryFile
        $stderrFile = New-TemporaryFile

        try {
            & fstar @commandArgs 1> $stdoutFile.FullName 2> $stderrFile.FullName
            $exitCode = $LASTEXITCODE

            $stdoutText = if ((Get-Item -LiteralPath $stdoutFile.FullName).Length -gt 0) {
                Get-Content -LiteralPath $stdoutFile.FullName -Raw
            } else {
                ""
            }

            $stderrText = if ((Get-Item -LiteralPath $stderrFile.FullName).Length -gt 0) {
                Get-Content -LiteralPath $stderrFile.FullName -Raw
            } else {
                ""
            }

            $outputParts = @($stdoutText.TrimEnd(), $stderrText.TrimEnd()) |
                Where-Object { $_ }
            $outputText = $outputParts -join [Environment]::NewLine
        } finally {
            Remove-Item -LiteralPath $stdoutFile.FullName, $stderrFile.FullName -Force -ErrorAction SilentlyContinue
        }

        $reportedErrors =
            $outputText -match '(?im)^\s*\* Error \d+\b' -or
            $outputText -match '(?im)\b[1-9][0-9]*\s+errors?\s+(was|were)\s+reported\b'

        if ($exitCode -eq 0 -and -not $reportedErrors) {
            $passed += 1
            Write-Host "  OK"
            continue
        }

        $failed.Add([pscustomobject]@{
            Path = $relativePath
            ExitCode = $exitCode
            Output = $outputText
        }) | Out-Null

        Write-Host "  FAILED"
        if ($outputText) {
            $outputText
        }

        if ($FailFast) {
            break
        }
    }
} finally {
    Pop-Location
}

Write-Host ""
$checked = $passed + $failed.Count
Write-Host "Summary: $passed passed, $($failed.Count) failed, $checked checked, $($proofFiles.Count) total"

if ($failed.Count -gt 0) {
    Write-Host ""
    Write-Host "Failed proofs:"
    foreach ($failure in $failed) {
        Write-Host "  - $($failure.Path)"
    }
    exit 1
}

exit 0

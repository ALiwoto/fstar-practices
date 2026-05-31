[CmdletBinding()]
param(
    [string[]] $ProofRoots = @("basic_proofs", "kaprekar_proofs"),
    [string[]] $FStarArgs = @(),
    [switch] $FailFast,
    [switch] $NoColor
)

$ErrorActionPreference = "Stop"

if ($PSScriptRoot) {
    $RepoRoot = Resolve-Path (Join-Path $PSScriptRoot "..")
} else {
    $RepoRoot = Resolve-Path "."
}

function Test-HostColorSupport {
    $privateData = $Host.PrivateData
    if ($null -eq $privateData) {
        return $false
    }

    $colorProperties = @(
        "FormatAccentColor",
        "ErrorAccentColor",
        "ErrorForegroundColor",
        "ErrorBackgroundColor",
        "WarningForegroundColor",
        "WarningBackgroundColor",
        "DebugForegroundColor",
        "DebugBackgroundColor",
        "VerboseForegroundColor",
        "VerboseBackgroundColor",
        "ProgressForegroundColor",
        "ProgressBackgroundColor"
    )

    foreach ($propertyName in $colorProperties) {
        if ($privateData.PSObject.Properties[$propertyName]) {
            return $true
        }
    }

    return $false
}

function Get-HostColor {
    param(
        [Parameter(Mandatory = $true)]
        [string] $PropertyName,

        [Parameter(Mandatory = $true)]
        [System.ConsoleColor] $Fallback
    )

    $privateData = $Host.PrivateData
    if ($null -eq $privateData) {
        return $Fallback
    }

    $property = $privateData.PSObject.Properties[$PropertyName]
    if ($property) {
        try {
            return [System.ConsoleColor] $property.Value
        } catch {
            return $Fallback
        }
    }

    return $Fallback
}

$UseColor = -not $NoColor -and (Test-HostColorSupport)
$Colors = @{
    Accent = Get-HostColor "ErrorAccentColor" ([System.ConsoleColor]::Cyan)
    Error = Get-HostColor "ErrorForegroundColor" ([System.ConsoleColor]::Red)
    Warning = Get-HostColor "WarningForegroundColor" ([System.ConsoleColor]::Yellow)
    Success = [System.ConsoleColor]::Green
}

function Write-Status {
    param(
        [Parameter(Mandatory = $true)]
        [AllowEmptyString()]
        [string] $Message,

        [System.ConsoleColor] $ForegroundColor = [System.ConsoleColor]::Gray
    )

    if ($UseColor) {
        Write-Host $Message -ForegroundColor $ForegroundColor
    } else {
        Write-Host $Message
    }
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
        Write-Status "WARNING: Proof root not found: $root" $Colors.Warning
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
        $relativeDirectory = ConvertTo-RepoRelativePath $file.DirectoryName
        Write-Status "[$index/$($proofFiles.Count)] Verifying $relativePath" $Colors.Accent

        $commandArgs = @($FStarArgs) + @("--include", $relativeDirectory, $relativePath)
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
            Write-Status "  OK" $Colors.Success
            continue
        }

        $failed.Add([pscustomobject]@{
            Path = $relativePath
            ExitCode = $exitCode
            Output = $outputText
        }) | Out-Null

        Write-Status "  FAILED" $Colors.Error
        if ($outputText) {
            Write-Status $outputText $Colors.Error
        }

        if ($FailFast) {
            break
        }
    }
} finally {
    Pop-Location
}

Write-Status ""
$checked = $passed + $failed.Count
$summaryColor = if ($failed.Count -gt 0) { $Colors.Error } else { $Colors.Success }
Write-Status "Summary: $passed passed, $($failed.Count) failed, $checked checked, $($proofFiles.Count) total" $summaryColor

if ($failed.Count -gt 0) {
    Write-Status ""
    Write-Status "Failed proofs:" $Colors.Error
    foreach ($failure in $failed) {
        Write-Status "  - $($failure.Path)" $Colors.Error
    }
    exit 1
}

exit 0

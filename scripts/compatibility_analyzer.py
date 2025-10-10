#!/usr/bin/env python3
"""
Compatibility Analyzer for curve25519-dalek-lite

This script analyzes different compatibility approaches in the codebase
and provides detailed comparisons of implementation strategies.
"""

import os
import re
from pathlib import Path
from typing import Dict, List, Set
from dataclasses import dataclass


@dataclass
class CompatibilityFeature:
    """Represents a compatibility feature found in the code."""
    name: str
    feature_type: str  # 'legacy', 'verus', 'api_evolution', 'backend'
    files: List[str]
    lines: List[int]
    description: str


class CompatibilityAnalyzer:
    """Analyzes compatibility features in the curve25519-dalek codebase."""
    
    def __init__(self, repo_root: str):
        self.repo_root = Path(repo_root)
        self.features: List[CompatibilityFeature] = []
        
    def analyze(self) -> Dict[str, List[CompatibilityFeature]]:
        """Perform comprehensive compatibility analysis."""
        
        # Analyze legacy compatibility features
        legacy_features = self._analyze_legacy_compatibility()
        
        # Analyze Verus compatibility modifications
        verus_features = self._analyze_verus_compatibility()
        
        # Analyze API evolution patterns
        api_features = self._analyze_api_evolution()
        
        # Analyze backend compatibility
        backend_features = self._analyze_backend_compatibility()
        
        return {
            'legacy': legacy_features,
            'verus': verus_features, 
            'api_evolution': api_features,
            'backend': backend_features
        }
    
    def _analyze_legacy_compatibility(self) -> List[CompatibilityFeature]:
        """Analyze legacy compatibility features."""
        features = []
        
        # Find legacy_compatibility feature usage
        cargo_toml = self.repo_root / "curve25519-dalek" / "Cargo.toml"
        if cargo_toml.exists():
            with open(cargo_toml, 'r') as f:
                lines = f.readlines()
                for i, line in enumerate(lines):
                    if 'legacy_compatibility' in line:
                        features.append(CompatibilityFeature(
                            name="legacy_compatibility_feature",
                            feature_type="legacy",
                            files=[str(cargo_toml)],
                            lines=[i + 1],
                            description="Feature flag for legacy compatibility"
                        ))
        
        # Find gated functions
        scalar_rs = self.repo_root / "curve25519-dalek" / "src" / "scalar.rs"
        if scalar_rs.exists():
            with open(scalar_rs, 'r') as f:
                lines = f.readlines()
                for i, line in enumerate(lines):
                    if 'cfg(feature = "legacy_compatibility")' in line:
                        features.append(CompatibilityFeature(
                            name="from_bits_function",
                            feature_type="legacy",
                            files=[str(scalar_rs)],
                            lines=[i + 1],
                            description="Legacy from_bits function (potentially unsafe)"
                        ))
        
        return features
    
    def _analyze_verus_compatibility(self) -> List[CompatibilityFeature]:
        """Analyze Verus verification system compatibility."""
        features = []
        
        # Find Verus-specific modifications
        for rust_file in self.repo_root.rglob("*.rs"):
            with open(rust_file, 'r') as f:
                lines = f.readlines()
                for i, line in enumerate(lines):
                    if 'VERIFICATION NOTE' in line:
                        # Extract the modification type from the comment
                        mod_type = self._extract_verus_modification_type(line)
                        features.append(CompatibilityFeature(
                            name=f"verus_modification_{mod_type}",
                            feature_type="verus",
                            files=[str(rust_file)],
                            lines=[i + 1],
                            description=f"Verus compatibility: {mod_type}"
                        ))
        
        return features
    
    def _analyze_api_evolution(self) -> List[CompatibilityFeature]:
        """Analyze API evolution and deprecation patterns."""
        features = []
        
        # Check CHANGELOG for breaking changes
        changelog = self.repo_root / "curve25519-dalek" / "CHANGELOG.md"
        if changelog.exists():
            with open(changelog, 'r') as f:
                content = f.read()
                
            # Find version sections with breaking changes
            version_pattern = r'### (\d+\.\d+\.\d+).*?(?=###|\Z)'
            versions = re.findall(version_pattern, content, re.DOTALL)
            
            if 'Breaking changes' in content:
                features.append(CompatibilityFeature(
                    name="api_breaking_changes",
                    feature_type="api_evolution",
                    files=[str(changelog)],
                    lines=[1],  # Would need more precise line detection
                    description="Documented breaking changes across versions"
                ))
        
        return features
    
    def _analyze_backend_compatibility(self) -> List[CompatibilityFeature]:
        """Analyze backend compatibility mechanisms."""
        features = []
        
        # Check build.rs for backend selection logic
        build_rs = self.repo_root / "curve25519-dalek" / "build.rs"
        if build_rs.exists():
            with open(build_rs, 'r') as f:
                lines = f.readlines()
                for i, line in enumerate(lines):
                    if 'determine_curve25519_dalek_bits' in line:
                        features.append(CompatibilityFeature(
                            name="automatic_backend_selection",
                            feature_type="backend",
                            files=[str(build_rs)],
                            lines=[i + 1],
                            description="Automatic backend selection based on target"
                        ))
                    elif 'is_capable_simd' in line:
                        features.append(CompatibilityFeature(
                            name="simd_capability_detection",
                            feature_type="backend",
                            files=[str(build_rs)],
                            lines=[i + 1],
                            description="SIMD capability detection for backend selection"
                        ))
        
        return features
    
    def _extract_verus_modification_type(self, line: str) -> str:
        """Extract the type of Verus modification from a comment."""
        line = line.lower()
        if 'wrapper function' in line:
            return "wrapper_function"
        elif 'manual' in line:
            return "manual_implementation"  
        elif 'loop' in line:
            return "loop_modification"
        elif 'helper function' in line:
            return "helper_function_relocation"
        else:
            return "general_modification"
    
    def generate_report(self, features_by_type: Dict[str, List[CompatibilityFeature]]) -> str:
        """Generate a detailed compatibility report."""
        report = "# Compatibility Analysis Report\n\n"
        
        for feature_type, features in features_by_type.items():
            report += f"## {feature_type.title()} Compatibility\n\n"
            
            if not features:
                report += "No specific features found.\n\n"
                continue
                
            for feature in features:
                report += f"### {feature.name}\n"
                report += f"- **Description**: {feature.description}\n"
                report += f"- **Files**: {', '.join(feature.files)}\n"
                report += f"- **Lines**: {', '.join(map(str, feature.lines))}\n\n"
        
        # Add summary statistics
        total_features = sum(len(features) for features in features_by_type.values())
        report += f"\n## Summary\n\n"
        report += f"Total compatibility features analyzed: {total_features}\n\n"
        
        for feature_type, features in features_by_type.items():
            report += f"- {feature_type.title()}: {len(features)} features\n"
        
        return report


def main():
    """Main entry point."""
    import argparse
    
    parser = argparse.ArgumentParser(description="Analyze compatibility features in curve25519-dalek-lite")
    parser.add_argument("--repo-root", default=".", help="Repository root path")
    parser.add_argument("--output", help="Output file for the report")
    
    args = parser.parse_args()
    
    analyzer = CompatibilityAnalyzer(args.repo_root)
    features = analyzer.analyze()
    report = analyzer.generate_report(features)
    
    if args.output:
        with open(args.output, 'w') as f:
            f.write(report)
        print(f"Report written to {args.output}")
    else:
        print(report)


if __name__ == "__main__":
    main()
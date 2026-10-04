"""Compile the concrete CompCert-memory INSTR and audit its semantic boundary."""
from pathlib import Path
import hashlib
import json
import subprocess

from audit_compiler import names
import polcert_core

ROOT = Path(__file__).resolve().parents[1]
MODULES = ["GuardMemoryRuntime", "GuardMemoryInstr", "GuardMemoryRectangles", "GuardMemoryPolyhedral",
           "GuardMemoryLoops", "GuardMemoryClightRectangles", "GuardMemoryPolyhedralRectangles",
           "GuardMemoryValidatedRectangles", "GuardMemoryCompiler", "GuardMemoryTilingProgress", "GuardMemoryArrayBackend",
           "GuardMemoryLoopTrace", "GuardMemoryTiledRectangles", "GuardMemoryTiledExecution",
           "GuardMemoryTiledClight", "GuardMemoryFlatArrayBackend", "GuardMemoryModeTiledClight",
           "GuardMemoryTiledCompiler", "GuardMemoryAffineDomains",
           "GuardMemoryConditionalLoops", "GuardMemoryCutExecution", "GuardMemoryCutClight",
           "GuardMemoryCutTiledClight", "GuardMemoryCutCompiler", "GuardMemoryTilingMultipleProgress", "GuardMemoryArrayFamilyBackend", "GuardMemoryIndexedTrace",
           "GuardMemorySequenceLoops", "GuardMemorySequenceClight", "GuardMemorySequencePolyhedral",
           "GuardMemorySequenceOrder", "GuardMemorySequenceExecution", "GuardMemorySequenceTiledClight",
           "GuardMemorySequenceCompiler", "GuardMemoryOperationsClight", "GuardMemoryOperationsTiledClight",
           "GuardMemoryOperationsCompiler", "GuardMemoryExtractorTrace", "GuardMemoryTraceUniqueness",
           "GuardMemoryExtractorCoverage", "GuardMemoryExtractorOrder", "GuardMemoryPointIsomorphism", "GuardMemoryDomainNormalization", "GuardMemoryExtractorProgress",
           "GuardMemoryCoordinateSwap", "GuardMemoryCoordinateShift", "GuardMemoryCoordinateSkew", "GuardMemoryCoordinateReflect", "GuardMemoryReindexedExtractor",
           "GuardMemoryDomainAlignment", "GuardMemoryExtractedTiling", "GuardMemoryEquivalentDomainsExtractor", "GuardMemoryAffineReindex", "GuardMemoryAffineMappedExtractor",
           "GuardMemoryProposedClight", "GuardMemoryProposedCompiler", "GuardMemoryGeneratedBounds", "GuardMemoryScheduleProducer",
           "GuardMemoryMultipleArrays", "GuardMemoryArraySeparation", "GuardMemoryRegistryBackend", "GuardMemoryRegistryTransfer", "GuardMemoryCrossArray", "GuardMemoryCrossInstruction", "GuardMemoryCopyArray", "GuardMemoryCopyInstruction", "GuardMemoryNamedOperations", "GuardMemoryNamedRegistrySource", "GuardMemoryRegistryGuard", "GuardMemoryNamedClight", "GuardMemoryNamedGuard", "GuardMemoryNamedCandidate", "GuardMemoryNamedChecker", "GuardMemoryNamedCompiler", "GuardMemoryNamedMappedChecker", "GuardMemoryNamedMappedCompiler", "GuardMemoryVariableCounterExit", "GuardMemoryRaggedLoops", "GuardMemoryRaggedClight", "GuardMemoryRaggedGuard", "GuardMemoryRaggedBackend", "GuardMemoryNamedRaggedSource", "GuardMemoryNamedRaggedCandidate", "GuardMemoryNamedRaggedChecker", "GuardMemoryTileRangeTrimming", "GuardMemoryRaggedTiling", "GuardMemoryNamedRaggedTiling", "GuardMemoryNamedRaggedCompiler", "GuardMemoryScheduledCompiler", "GuardMemoryAffineSourceExpressions", "GuardMemoryAffineSourceReifier", "GuardMemoryAffineSourceValuation", "GuardMemoryAffineSourceLoop", "GuardMemoryAffineSourceContext", "GuardMemoryAffineSourceEndpoints", "GuardMemoryParametricSourceClight", "GuardMemoryParametricLoops", "GuardMemoryNamedParametricSource", "GuardMemoryParametricWidth", "GuardMemoryParametricRestore", "GuardMemoryParametricGuard", "GuardMemoryParametricSourceDomain", "GuardMemoryParametricSyntax", "GuardMemoryParametricChecker", "GuardMemoryParametricTiling", "GuardMemoryParametricCandidate", "GuardMemoryParametricCompiler", "GuardMemoryCommonLayout", "GuardMemoryLayoutCopy", "GuardMemoryLayoutCopyInstruction", "GuardMemoryLayoutCopyRegistry", "GuardMemoryCopyLayoutRegistry", "GuardMemoryLayoutCopySource", "GuardMemoryLayoutCopyDomain", "GuardMemoryParametricInstructionChecker", "GuardMemoryParametricInstructionTiling", "GuardMemoryLayoutCopyCandidate", "GuardMemoryLayoutCopySyntax", "GuardMemoryLayoutCopyCompiler", "GuardMemoryParametricBody", "GuardMemoryNamedBodyModel", "GuardMemoryLayoutCopyBodyModel", "GuardMemoryParametricBodyDomain", "GuardMemoryParametricBodyCandidate", "GuardMemoryParametricRegion", "GuardMemoryLayoutRegistry", "GuardMemoryLayoutCopyRegistryPoint", "GuardMemoryLayoutOperations", "GuardMemoryLayoutSequence", "GuardMemoryLayoutRanges", "GuardMemoryLayoutBodyModel", "GuardMemoryLayoutSyntax", "GuardMemoryAffineAccessExpressions", "GuardMemoryAffineAccess", "GuardMemoryAffineCopy", "GuardMemoryGeneralLayoutOperations", "GuardMemoryGeneralLayoutSequence", "GuardMemoryGeneralLayoutBodyModel", "GuardMemoryGeneralLayoutSyntax", "GuardMemoryAccessAnchors", "GuardMemoryOffsetAccessRanges", "GuardMemoryOffsetBodyModel", "GuardMemoryOffsetSyntax", "GuardMemorySourceValues", "GuardMemoryAffineReadRegistry", "GuardMemoryAffineCompute", "GuardMemoryComputeAnchors", "GuardMemoryComputeSequence", "GuardMemoryComputeBodyModel", "GuardMemoryComputeSyntax", "GuardMemoryParametricRegionInstances", "GuardMemoryParametricRegionCompiler", "GuardMemoryParametricRegionRestriction", "GuardMemoryParametricWidthSearch", "GuardMemorySettledCountedLoop", "GuardMemoryControlSettle", "GuardMemoryNaryAffineExpressions", "GuardMemoryNaryRanges", "GuardMemorySignedRanges", "GuardMemoryNaryAffineAccess", "GuardMemoryNaryAccessCheck", "GuardMemoryNarySourceValues", "GuardMemoryNaryReadRegistry", "GuardMemoryNaryCompute", "GuardMemoryNaryLoops", "GuardMemoryNaryAnchors", "GuardMemoryNarySequence", "GuardMemoryNaryComputeSyntax", "GuardMemoryNaryBodyModel", "GuardMemoryNaryLift", "GuardMemoryTripleSource", "GuardMemoryTripleWords", "GuardMemoryTripleBody", "GuardMemoryTripleSyntax", "GuardMemoryTripleGuard", "GuardMemoryTripleDomain", "GuardMemoryTripleRestore", "GuardMemoryTripleChecker", "GuardMemoryTripleTiling", "GuardMemoryTripleCandidate", "GuardMemoryTripleCompiler", "GuardMemoryRecursiveSource", "GuardMemoryRecursiveExecution", "GuardMemoryRecursiveBody", "GuardMemoryRecursiveSyntax", "GuardMemoryRecursiveGuard", "GuardMemoryRecursiveWords", "GuardMemoryRecursiveDomain", "GuardMemoryRecursiveRestore", "GuardMemoryRecursiveChecker", "GuardMemoryRecursiveTiling", "GuardMemoryRecursiveCandidate", "GuardMemoryRecursiveCompiler", "GuardMemoryBufferOffsets", "GuardMemoryFramedNested", "GuardMemoryRecursiveFramedExecution", "GuardMemoryRecursiveFirstLeaf", "GuardMemoryPointerAccess", "GuardMemoryPointerSourceAccess", "GuardMemorySourceValueInterface", "GuardMemoryPointerBackend", "GuardMemoryPointerNaryAccess", "GuardMemoryPointerCompute", "GuardMemoryPointerRegistry", "GuardMemoryPointerComputeSyntax", "GuardMemoryPointerSequence", "GuardMemoryPointerSyntax", "GuardMemoryPointerBody", "GuardMemoryPointerDomain", "GuardMemoryPointerCandidate", "GuardMemoryPointerConditionSearch", "GuardMemoryPointerCompiler", "GuardMemoryInstructionPadding", "GuardMemoryScalarLoops", "GuardMemorySourceParameters", "GuardMemoryScalarLift", "GuardMemoryScalarAccess", "GuardMemoryScalarChecker", "GuardMemoryScalarPointerCompute", "GuardMemoryScalarPointerRegistry", "GuardMemoryScalarPointerComputeSyntax", "GuardMemoryScalarPointerSequence", "GuardMemoryScalarPointerSyntax", "GuardMemoryScalarPointerBody", "GuardMemoryScalarPointerDomain", "GuardMemoryScalarPointerBounds", "GuardMemoryScalarPointerCandidate", "GuardMemoryScalarCandidates", "GuardMemoryScalarTiling", "GuardMemoryScalarPointerConditionSearch", "GuardMemoryScalarPointerCompiler", "GuardMemoryScalarArrayCompute", "GuardMemoryScalarArrayComputeSyntax", "GuardMemoryScalarArraySequence", "GuardMemoryScalarArrayAnchors", "GuardMemoryScalarArraySyntax", "GuardMemoryScalarArrayBody", "GuardMemoryScalarArrayDomain", "GuardMemoryScalarArrayCandidate", "GuardMemoryScalarArrayConditionSearch", "GuardMemoryScalarArrayCompiler", "GuardMemoryUnifiedCompiler"]
MULTI_POINTER_MODULES = ['GuardMemoryPointerCellComparison', 'GuardMemoryFootprintRestriction', 'GuardMemoryFootprintCapabilities', 'GuardMemoryFiniteFootprint', 'GuardMemoryFiniteAliasCondition', 'GuardMemoryActivatedAliasCondition', 'GuardMemoryMultiPointerCells', 'GuardMemoryMultiPointerAccess', 'GuardMemoryMultiPointerCompute', 'GuardMemoryMultiPointerRegistry', 'GuardMemoryMultiPointerSequence', 'GuardMemoryMultiPointerIdentifiers', 'GuardMemoryMultiPointerComputeSyntax', 'GuardMemoryMultiPointerSyntax', 'GuardMemoryMultiPointerBody', 'GuardMemoryMultiPointerDomain', 'GuardMemoryMultiPointerBackend', 'GuardMemoryRectangularFootprint', 'GuardMemoryCoordinateActivation', 'GuardMemoryActivatedRectangle', 'GuardMemoryMultiPointerFootprint', 'GuardMemoryMultiPointerRegionGuard', 'GuardMemoryMultiPointerCandidate', 'GuardMemoryMultiPointerConditionSearch', 'GuardMemorySequentialCondition', 'GuardMemoryCompactAliasCondition', 'GuardMemoryMultiPointerCompiler', 'GuardMemoryMultiPointerGuard']
MODULES[-1:-1] = MULTI_POINTER_MODULES
LOOP_ALIAS_MODULES = ['GuardMemoryProjectedCondition', 'GuardMemoryCrossPointerSeparation', 'GuardMemoryBooleanScan', 'GuardMemoryPointerRangeScan', 'GuardMemoryMultiPointerProjectedCandidate', 'GuardMemoryLinearPointerSyntax', 'GuardMemoryLinearPointerPair', 'GuardMemoryLoopGuardFrame', 'GuardMemoryLinearPointerGuard', 'GuardMemoryLinearPointerCompiler']
MODULES[-1:-1] = LOOP_ALIAS_MODULES
AFFINE_ALIAS_MODULES = ['GuardMemoryStatefulLanguage', 'GuardMemoryStatefulEntry', 'GuardMemoryStatefulRule', 'GuardMemoryStatefulComposition', 'GuardMemoryAffineRenaming', 'GuardMemoryAffineRangeAddress', 'GuardMemoryAffinePairScan', 'GuardMemoryAffineEndpointMath', 'GuardMemoryAffineEndpointCells', 'GuardMemoryAffineEndpointScan', 'GuardMemoryAffinePairChoice', 'GuardMemoryAffinePointerSyntax', 'GuardMemoryAffinePointerPairs', 'GuardMemoryAffinePointerScan', 'GuardMemoryAffinePointerFrame', 'GuardMemoryAffinePointerGuard', 'GuardMemoryAffinePointerCompiler']
MODULES[-1:-1] = AFFINE_ALIAS_MODULES
AXIS_ALIAS_MODULES = ['GuardMemoryBooleanRectangle', 'GuardMemoryBooleanRectangleExecution', 'GuardMemoryAffineAxisRenaming', 'GuardMemoryAffineAxisAddress', 'GuardMemoryAffineAxisPairScan', 'GuardMemoryAxisPointerFootprint', 'GuardMemoryAxisPointerPairs', 'GuardMemoryAxisPointerScan', 'GuardMemoryAxisPointerFrame', 'GuardMemoryAxisPointerGuard', 'GuardMemoryAxisPointerCompiler', 'GuardMemoryAxisPointerServices', 'GuardMemoryAxisPointerDescribe']
AXIS_BOUNDARY_MODULES = ['GuardMemoryAxisBoundaryMath', 'GuardMemoryAxisRepeatedRenaming', 'GuardMemoryAxisRepeatedAddress', 'GuardMemoryAxisBoundaryNames', 'GuardMemoryAxisBoundaryCells', 'GuardMemoryAxisBoundaryTest', 'GuardMemoryAxisBoundaryScan', 'GuardMemoryAxisBoundaryMasks', 'GuardMemoryAxisBoundaryPair', 'GuardMemoryAxisPairChoice']
AXIS_ALIAS_MODULES[6:6] = AXIS_BOUNDARY_MODULES
MODULES[-1:-1] = AXIS_ALIAS_MODULES
VECTOR_AXIS_MODULES = ['GuardMemoryVectorBounds', 'GuardMemoryVectorDomain', 'GuardMemoryVectorGuard', 'GuardMemoryVectorChecker', 'GuardMemoryVectorPointerBounds', 'GuardMemoryVectorPointerSyntax', 'GuardMemoryVectorPointerBody', 'GuardMemoryVectorPointerDomain', 'GuardMemoryVectorTiling', 'GuardMemoryVectorPointerFootprint', 'GuardMemoryVectorPointerProjectedCandidate', 'GuardMemoryVectorAxisFootprint', 'GuardMemoryVectorAxisPairs', 'GuardMemoryVectorAxisScan', 'GuardMemoryVectorRuntimeFrame', 'GuardMemoryVectorAxisFrame', 'GuardMemoryVectorAxisGuard', 'GuardMemoryVectorAxisCompiler', 'GuardMemoryVectorAxisServices', 'GuardMemoryVectorAxisDescribe']
MODULES[-1:-1] = VECTOR_AXIS_MODULES
ADDRESS_PARAM_MODULES = ['GuardMemoryPointerDefinedIndex', 'GuardMemoryPointerSourceWords', 'GuardMemoryParamAxisPairScan', 'GuardMemoryParameterRanges', 'GuardMemoryParamPointerSyntax', 'GuardMemoryParamPointerBody', 'GuardMemoryParamPointerDomain', 'GuardMemoryParamPointerHeader', 'GuardMemoryParamPointerBounds', 'GuardMemoryParamPointerProjectedCandidate', 'GuardMemoryParamPointerFootprint', 'GuardMemoryParamAxisFootprint', 'GuardMemoryParamAxisPairs', 'GuardMemoryParamAxisScan', 'GuardMemoryParamRuntimeFrame', 'GuardMemoryParamAxisFrame', 'GuardMemoryParamAxisGuard', 'GuardMemoryParamAxisCompiler', 'GuardMemoryParamAxisServices', 'GuardMemoryParamAxisDescribe']
PARAM_BOUNDARY_MODULES = ['GuardMemoryParamBoundaryMath', 'GuardMemoryParamBoundaryCells', 'GuardMemoryParamBoundaryTest', 'GuardMemoryParamBoundaryScan', 'GuardMemoryParamBoundaryMasks', 'GuardMemoryParamBoundaryPair', 'GuardMemoryParamAxisPairChoice']
ADDRESS_PARAM_MODULES[ADDRESS_PARAM_MODULES.index('GuardMemoryParamAxisScan'):ADDRESS_PARAM_MODULES.index('GuardMemoryParamAxisScan')] = PARAM_BOUNDARY_MODULES
MODULES[-1:-1] = ADDRESS_PARAM_MODULES
VERSION_MODULES = ['GuardMemoryStatefulVersions', 'GuardMemoryVersionFamily', 'GuardMemoryParamVersionComponents', 'GuardMemoryParamVersionServices', 'GuardMemoryParamVersionGroups']
MODULES[-1:-1] = VERSION_MODULES
PREFILTER_MODULES = ['GuardMemoryCheckPrefix', 'GuardMemoryPrefilterVersions', 'GuardMemoryPrefilterComponents', 'GuardMemoryPrefilterGroups']
MODULES[-1:-1] = PREFILTER_MODULES
STATEFUL_CORE_MODULES = ['StatefulGuard', 'StatefulGuardComposition', 'StatefulGuardVersions']
LOWERING_MODULES = ["ClightPositiveDivision", "PolCertLoopGuard", "PolCertAffineClight", "PolCertAffineGuard",
                    "PolCertCountedClight", "PolCertClightBody", "PolCertNestedClight"]
DIRECTORY = ROOT / "adapters" / "compcert-memory"
WORK = ROOT / "build" / "guard-memory-assumptions"


def main():
    polcert_core.select_profile("optimizer")
    report = json.loads(polcert_core.artifact("report.json").read_text())
    if (report["status"] != "compiled" or report["source_manifest_sha256"] !=
            hashlib.sha256(polcert_core.MANIFEST.read_bytes()).hexdigest()):
        raise SystemExit("build the locked PolCert optimizer proof profile first")
    flags = [*polcert_core.load_flags(), "-Q", str(DIRECTORY), "GuardMemory"]
    WORK.mkdir(parents=True, exist_ok=True)
    logs = []
    for module in STATEFUL_CORE_MODULES:
        print("Compiling abstract stateful core", module, flush=True)
        result = subprocess.run(["rocq", "compile", *flags, str(ROOT / "theories" / (module + ".v"))],
                                cwd=ROOT, check=True, text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT)
        logs.append(result.stdout)
    for module in LOWERING_MODULES:
        print("Compiling lowering", module, flush=True)
        result = subprocess.run(["rocq", "compile", *flags, str(ROOT / "theories" / (module + ".v"))],
                                cwd=ROOT, check=True, text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT)
        logs.append(result.stdout)
    for module in MODULES:
        print("Compiling memory adapter", module, flush=True)
        result = subprocess.run(["rocq", "compile", *flags, str(DIRECTORY / (module + ".v"))],
                                cwd=ROOT, check=True, text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT)
        logs.append(result.stdout)
    (WORK / "build.log").write_text("\n".join(logs))
    audit = WORK / "Audit.v"
    audit.write_text("""From compcert.driver Require Import Compiler.
From Guard Require Import StatefulGuard StatefulGuardComposition StatefulGuardVersions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryRectangles GuardMemoryPolyhedral
  GuardMemoryLoops GuardMemoryClightRectangles GuardMemoryPolyhedralRectangles
  GuardMemoryValidatedRectangles GuardMemoryCompiler GuardMemoryTilingProgress GuardMemoryArrayBackend
  GuardMemoryLoopTrace GuardMemoryTiledRectangles GuardMemoryTiledExecution GuardMemoryTiledClight
  GuardMemoryFlatArrayBackend GuardMemoryModeTiledClight GuardMemoryTiledCompiler
  GuardMemoryAffineDomains GuardMemoryConditionalLoops GuardMemoryCutExecution GuardMemoryCutClight
  GuardMemoryCutTiledClight GuardMemoryCutCompiler GuardMemoryTilingMultipleProgress
  GuardMemoryArrayFamilyBackend GuardMemoryIndexedTrace GuardMemorySequenceLoops GuardMemorySequenceClight
  GuardMemorySequencePolyhedral GuardMemorySequenceOrder GuardMemorySequenceExecution
  GuardMemorySequenceTiledClight GuardMemorySequenceCompiler GuardMemoryOperationsClight
  GuardMemoryOperationsTiledClight GuardMemoryOperationsCompiler GuardMemoryExtractorTrace GuardMemoryTraceUniqueness
  GuardMemoryExtractorCoverage GuardMemoryExtractorOrder GuardMemoryPointIsomorphism GuardMemoryDomainNormalization GuardMemoryExtractorProgress GuardMemoryCoordinateSwap GuardMemoryCoordinateShift GuardMemoryCoordinateSkew GuardMemoryCoordinateReflect GuardMemoryReindexedExtractor GuardMemoryDomainAlignment GuardMemoryExtractedTiling GuardMemoryEquivalentDomainsExtractor GuardMemoryAffineReindex GuardMemoryAffineMappedExtractor
  GuardMemoryProposedClight GuardMemoryProposedCompiler GuardMemoryGeneratedBounds GuardMemoryScheduleProducer
  GuardMemoryMultipleArrays GuardMemoryArraySeparation GuardMemoryRegistryBackend GuardMemoryRegistryTransfer GuardMemoryCrossArray GuardMemoryCrossInstruction GuardMemoryCopyArray GuardMemoryCopyInstruction GuardMemoryNamedOperations GuardMemoryNamedRegistrySource GuardMemoryRegistryGuard GuardMemoryNamedClight GuardMemoryNamedGuard GuardMemoryNamedCandidate GuardMemoryNamedChecker GuardMemoryNamedCompiler GuardMemoryNamedMappedChecker GuardMemoryNamedMappedCompiler GuardMemoryVariableCounterExit GuardMemoryRaggedLoops GuardMemoryRaggedClight GuardMemoryRaggedGuard GuardMemoryRaggedBackend GuardMemoryNamedRaggedSource GuardMemoryNamedRaggedCandidate GuardMemoryNamedRaggedChecker GuardMemoryTileRangeTrimming GuardMemoryRaggedTiling GuardMemoryNamedRaggedTiling GuardMemoryNamedRaggedCompiler GuardMemoryScheduledCompiler GuardMemoryAffineSourceExpressions GuardMemoryAffineSourceReifier GuardMemoryAffineSourceValuation GuardMemoryAffineSourceLoop GuardMemoryAffineSourceContext GuardMemoryAffineSourceEndpoints GuardMemoryParametricSourceClight GuardMemoryParametricLoops GuardMemoryNamedParametricSource GuardMemoryParametricWidth GuardMemoryParametricRestore GuardMemoryParametricGuard GuardMemoryParametricSourceDomain GuardMemoryParametricSyntax GuardMemoryParametricChecker GuardMemoryParametricTiling GuardMemoryParametricCandidate GuardMemoryParametricCompiler GuardMemoryCommonLayout GuardMemoryLayoutCopy GuardMemoryLayoutCopyInstruction GuardMemoryLayoutCopyRegistry GuardMemoryCopyLayoutRegistry GuardMemoryLayoutCopySource GuardMemoryLayoutCopyDomain GuardMemoryParametricInstructionChecker GuardMemoryParametricInstructionTiling GuardMemoryLayoutCopyCandidate GuardMemoryLayoutCopySyntax GuardMemoryLayoutCopyCompiler GuardMemoryParametricBody GuardMemoryNamedBodyModel GuardMemoryLayoutCopyBodyModel GuardMemoryParametricBodyDomain GuardMemoryParametricBodyCandidate GuardMemoryParametricRegion GuardMemoryLayoutRegistry GuardMemoryLayoutCopyRegistryPoint GuardMemoryLayoutOperations GuardMemoryLayoutSequence GuardMemoryLayoutRanges GuardMemoryLayoutBodyModel GuardMemoryLayoutSyntax GuardMemoryAffineAccessExpressions GuardMemoryAffineAccess GuardMemoryAffineCopy GuardMemoryGeneralLayoutOperations GuardMemoryGeneralLayoutSequence GuardMemoryGeneralLayoutBodyModel GuardMemoryGeneralLayoutSyntax GuardMemoryAccessAnchors GuardMemoryOffsetAccessRanges GuardMemoryOffsetBodyModel GuardMemoryOffsetSyntax GuardMemorySourceValues GuardMemoryAffineReadRegistry GuardMemoryAffineCompute GuardMemoryComputeAnchors GuardMemoryComputeSequence GuardMemoryComputeBodyModel GuardMemoryComputeSyntax GuardMemoryParametricRegionInstances GuardMemoryParametricRegionCompiler GuardMemoryParametricRegionRestriction GuardMemoryParametricWidthSearch GuardMemorySettledCountedLoop GuardMemoryControlSettle GuardMemoryNaryAffineExpressions GuardMemoryNaryRanges GuardMemorySignedRanges GuardMemoryNaryAffineAccess GuardMemoryNaryAccessCheck GuardMemoryNarySourceValues GuardMemoryNaryReadRegistry GuardMemoryNaryCompute GuardMemoryNaryLoops GuardMemoryNaryAnchors GuardMemoryNarySequence GuardMemoryNaryComputeSyntax GuardMemoryNaryBodyModel GuardMemoryNaryLift GuardMemoryTripleSource GuardMemoryTripleWords GuardMemoryTripleBody GuardMemoryTripleSyntax GuardMemoryTripleGuard GuardMemoryTripleDomain GuardMemoryTripleRestore GuardMemoryTripleChecker GuardMemoryTripleTiling GuardMemoryTripleCandidate GuardMemoryTripleCompiler GuardMemoryRecursiveSource GuardMemoryRecursiveExecution GuardMemoryRecursiveBody GuardMemoryRecursiveSyntax GuardMemoryRecursiveGuard GuardMemoryRecursiveWords GuardMemoryRecursiveDomain GuardMemoryRecursiveRestore GuardMemoryRecursiveChecker GuardMemoryRecursiveTiling GuardMemoryRecursiveCandidate GuardMemoryRecursiveCompiler GuardMemoryBufferOffsets GuardMemoryFramedNested GuardMemoryRecursiveFramedExecution GuardMemoryRecursiveFirstLeaf GuardMemoryPointerAccess GuardMemoryPointerSourceAccess GuardMemorySourceValueInterface GuardMemoryPointerBackend GuardMemoryPointerNaryAccess GuardMemoryPointerCompute GuardMemoryPointerRegistry GuardMemoryPointerComputeSyntax GuardMemoryPointerSequence GuardMemoryPointerSyntax GuardMemoryPointerBody GuardMemoryPointerDomain GuardMemoryPointerCandidate GuardMemoryPointerConditionSearch GuardMemoryPointerCompiler GuardMemoryInstructionPadding GuardMemoryScalarLoops GuardMemorySourceParameters GuardMemoryScalarLift GuardMemoryScalarAccess GuardMemoryScalarChecker GuardMemoryScalarPointerCompute GuardMemoryScalarPointerRegistry GuardMemoryScalarPointerComputeSyntax GuardMemoryScalarPointerSequence GuardMemoryScalarPointerSyntax GuardMemoryScalarPointerBody GuardMemoryScalarPointerDomain GuardMemoryScalarPointerBounds GuardMemoryScalarPointerCandidate GuardMemoryScalarCandidates GuardMemoryScalarTiling GuardMemoryScalarPointerConditionSearch GuardMemoryScalarPointerCompiler GuardMemoryScalarArrayCompute GuardMemoryScalarArrayComputeSyntax GuardMemoryScalarArraySequence GuardMemoryScalarArrayAnchors GuardMemoryScalarArraySyntax GuardMemoryScalarArrayBody GuardMemoryScalarArrayDomain GuardMemoryScalarArrayCandidate GuardMemoryScalarArrayConditionSearch GuardMemoryScalarArrayCompiler GuardMemoryUnifiedCompiler.
From GuardMemory Require Import GuardMemoryPointerCellComparison GuardMemoryFootprintRestriction GuardMemoryFootprintCapabilities GuardMemoryFiniteFootprint GuardMemoryFiniteAliasCondition GuardMemoryActivatedAliasCondition GuardMemoryMultiPointerCells GuardMemoryMultiPointerAccess GuardMemoryMultiPointerCompute GuardMemoryMultiPointerRegistry GuardMemoryMultiPointerSequence GuardMemoryMultiPointerIdentifiers GuardMemoryMultiPointerComputeSyntax GuardMemoryMultiPointerSyntax GuardMemoryMultiPointerBody GuardMemoryMultiPointerDomain GuardMemoryMultiPointerBackend GuardMemoryRectangularFootprint GuardMemoryCoordinateActivation GuardMemoryActivatedRectangle GuardMemoryMultiPointerFootprint GuardMemoryMultiPointerRegionGuard GuardMemoryMultiPointerCandidate GuardMemoryMultiPointerConditionSearch GuardMemorySequentialCondition GuardMemoryCompactAliasCondition GuardMemoryMultiPointerCompiler GuardMemoryMultiPointerGuard.
From GuardMemory Require Import GuardMemoryProjectedCondition GuardMemoryCrossPointerSeparation GuardMemoryBooleanScan GuardMemoryPointerRangeScan GuardMemoryMultiPointerProjectedCandidate GuardMemoryLinearPointerSyntax GuardMemoryLinearPointerPair GuardMemoryLoopGuardFrame GuardMemoryLinearPointerGuard GuardMemoryLinearPointerCompiler.
From GuardMemory Require Import GuardMemoryAffineEndpointMath GuardMemoryAffineEndpointCells GuardMemoryAffineEndpointScan GuardMemoryAffinePairChoice.
From GuardMemory Require Import GuardMemoryBooleanRectangle GuardMemoryBooleanRectangleExecution GuardMemoryAffineAxisRenaming GuardMemoryAffineAxisAddress GuardMemoryAffineAxisPairScan GuardMemoryAxisPointerFootprint GuardMemoryAxisPointerPairs GuardMemoryAxisPointerScan GuardMemoryAxisPointerFrame GuardMemoryAxisPointerGuard GuardMemoryAxisPointerCompiler GuardMemoryAxisPointerServices GuardMemoryAxisPointerDescribe.
From GuardMemory Require Import GuardMemoryAxisBoundaryMath GuardMemoryAxisRepeatedRenaming GuardMemoryAxisRepeatedAddress GuardMemoryAxisBoundaryNames GuardMemoryAxisBoundaryCells GuardMemoryAxisBoundaryTest GuardMemoryAxisBoundaryScan GuardMemoryAxisBoundaryMasks GuardMemoryAxisBoundaryPair GuardMemoryAxisPairChoice.
From GuardMemory Require Import GuardMemoryStatefulLanguage GuardMemoryStatefulEntry GuardMemoryStatefulRule GuardMemoryStatefulComposition GuardMemoryAffineRenaming GuardMemoryAffineRangeAddress GuardMemoryAffinePairScan GuardMemoryAffinePointerSyntax GuardMemoryAffinePointerPairs GuardMemoryAffinePointerScan GuardMemoryAffinePointerFrame GuardMemoryAffinePointerGuard GuardMemoryAffinePointerCompiler.
From GuardMemory Require Import GuardMemoryVectorBounds GuardMemoryVectorDomain GuardMemoryVectorGuard GuardMemoryVectorChecker GuardMemoryVectorPointerBounds GuardMemoryVectorPointerSyntax GuardMemoryVectorPointerBody GuardMemoryVectorPointerDomain GuardMemoryVectorTiling GuardMemoryVectorPointerFootprint GuardMemoryVectorPointerProjectedCandidate GuardMemoryVectorAxisFootprint GuardMemoryVectorAxisPairs GuardMemoryVectorAxisScan GuardMemoryVectorRuntimeFrame GuardMemoryVectorAxisFrame GuardMemoryVectorAxisGuard GuardMemoryVectorAxisCompiler GuardMemoryVectorAxisServices GuardMemoryVectorAxisDescribe.
From GuardMemory Require Import GuardMemoryParamBoundaryMath GuardMemoryParamBoundaryCells GuardMemoryParamBoundaryTest GuardMemoryParamBoundaryScan GuardMemoryParamBoundaryMasks GuardMemoryParamBoundaryPair GuardMemoryParamAxisPairChoice.
From GuardMemory Require Import GuardMemoryStatefulVersions GuardMemoryVersionFamily GuardMemoryParamVersionComponents GuardMemoryParamVersionServices GuardMemoryParamVersionGroups.
From GuardMemory Require Import GuardMemoryCheckPrefix GuardMemoryPrefilterVersions GuardMemoryPrefilterComponents GuardMemoryPrefilterGroups.
From GuardMemory Require Import GuardMemoryPointerDefinedIndex GuardMemoryPointerSourceWords GuardMemoryParamAxisPairScan GuardMemoryParameterRanges GuardMemoryParamPointerSyntax GuardMemoryParamPointerBody GuardMemoryParamPointerDomain GuardMemoryParamPointerHeader GuardMemoryParamPointerBounds GuardMemoryParamPointerProjectedCandidate GuardMemoryParamPointerFootprint GuardMemoryParamAxisFootprint GuardMemoryParamAxisPairs GuardMemoryParamAxisScan GuardMemoryParamRuntimeFrame GuardMemoryParamAxisFrame GuardMemoryParamAxisGuard GuardMemoryParamAxisCompiler GuardMemoryParamAxisServices GuardMemoryParamAxisDescribe.
Goal True. idtac "MEM_CC_BASE". exact I. Qed.
Print Assumptions Compiler.transf_c_program_correct.
Goal True. idtac "MEM_VALIDATOR_BASE". exact I. Qed.
Print Assumptions GuardMemoryValidator.validate_correct.
Print Assumptions GuardMemoryValidator.validate_tiling_correct.
Print Assumptions GuardMemoryTilingValidator.checked_tiling_validate_poly_correct.
Goal True. idtac "MEM_STATEFUL_CORE". exact I. Qed.
Print Assumptions stateful_guard_preservation.
Print Assumptions stateful_versions_preservation.
Print Assumptions projected_guard_conjunction.
Goal True. idtac "MEM_AFFINE_GUARD_MATH". exact I. Qed.
Print Assumptions memory_affine_endpoint_check_complete.
Print Assumptions memory_affine_pair_fast_complete.
Print Assumptions memory_affine_pair_choice_complete.
Print Assumptions memory_affine_pair_choice_frame.
Print Assumptions memory_boolean_rectangle_enumeration.
Print Assumptions memory_affine_axis_rename_layout.
Print Assumptions memory_axis_pointer_runtime_footprint.
Print Assumptions memory_axis_pointer_accesses_encoding.
Print Assumptions memory_axis_access_pair_check_frame.
Print Assumptions memory_axis_boundary_check_complete.
Print Assumptions memory_axis_boundary_masks_length.
Print Assumptions memory_axis_boundary_names_bindings.
Print Assumptions memory_affine_axis_boundary_pair_exact.
Print Assumptions memory_axis_boundary_masks_valid.
Print Assumptions memory_vector_bounds_sound.
Print Assumptions memory_register_range_monotone.
Print Assumptions memory_vector_bounds_domain_from_uniform.
Print Assumptions memory_vector_parameter_data.
Print Assumptions memory_vector_guard_sound.
Print Assumptions memory_vector_validator_count_scalar_ranges.
Print Assumptions memory_vector_encoder_count_scalar_ranges.
Print Assumptions memory_vector_bounds_accept_temp_frame.
Print Assumptions memory_vector_guard_accept_temp_frame.
Print Assumptions check_memory_param_pointer_region.
Print Assumptions memory_param_boundary_specialize_value.
Print Assumptions memory_param_boundary_overlap.
Print Assumptions memory_param_rectangle_active_ext.
Print Assumptions memory_param_axis_full_specialize.
Print Assumptions memory_param_axis_boundary_specialize.
Print Assumptions memory_param_axis_boundary_pair_exact.
Print Assumptions memory_parameter_range_sound.
Print Assumptions memory_parameter_ranges_sound.
Print Assumptions memory_param_validator_count_parameter_scalar_ranges.
Print Assumptions memory_param_encoder_count_parameter_scalar_ranges.
Print Assumptions memory_parameter_ranges_accept_temp_frame.
Print Assumptions memory_param_pointer_header_accept_temp_frame.
Goal True. idtac "MEM_PHYSICAL_REGISTRY". exact I. Qed.
Print Assumptions flat_array_locations_nonalias.
Print Assumptions memory_pointer_buffer_locations_nonalias.
Print Assumptions memory_array_registry_nonalias.
Print Assumptions memory_array_base_comparison.
Print Assumptions memory_blocks_unique_correct.
Print Assumptions memory_multi_pointer_same_identifier_nonalias.
Print Assumptions memory_cross_pointer_separation_suffices.
Goal True. idtac "MEM_INSTRUCTION". exact I. Qed.
Print Assumptions GuardMemoryInstr.bc_condition_implie_permutbility.
Print Assumptions GuardMemoryInstr.access_function_checker_correct.
Print Assumptions resolved_instruction_execution.
Print Assumptions rect_memory_write_execution.
Print Assumptions rect_memory_write_clight_decode.
Print Assumptions rect_memory_update_execution.
Print Assumptions rect_memory_row_update_execution.
Print Assumptions memory_rectangle_loop_iterations.
Print Assumptions memory_rectangle_lift.
Print Assumptions memory_rectangle_source_clight_decode.
Print Assumptions memory_rectangle_candidate_clight_encode.
Print Assumptions array_write_backend.
Print Assumptions compile_memory_array_loop_correct.
Print Assumptions memory_loop_trace_correct.
Print Assumptions rectangle_tiled_loop_points.
Print Assumptions compile_memory_cut_condition_evaluation.
Print Assumptions memory_cut_source_clight_decode.
Print Assumptions array_family_source_clight_decode.
Print Assumptions array_family_backend.
Print Assumptions indexed_memory_loop_execution.
Print Assumptions memory_sequence_tiled_loop_points.
Print Assumptions array_operations_source_clight_decode.
Print Assumptions flat_array_instruction_backend.
Print Assumptions compile_memory_flat_array_loop_within_correct.
Print Assumptions memory_extractor_static_sites.
Print Assumptions memory_extractor_trace_metadata.
Print Assumptions memory_extracted_trace_execution.
Print Assumptions memory_extracted_trace_coverage_iff.
Print Assumptions memory_extracted_trace_points_unique.
Print Assumptions memory_extracted_trace_points_sorted.
Print Assumptions memory_extractor_execution_at.
Print Assumptions memory_point_isomorphism_execution.
Print Assumptions memory_domain_normalization_execution.
Print Assumptions memory_coordinate_swap_execution.
Print Assumptions memory_coordinate_shift_execution.
Print Assumptions memory_coordinate_skew_execution.
Print Assumptions memory_coordinate_reflect_execution.
Print Assumptions memory_affine_reindexed_execution.
Print Assumptions memory_reindexed_execution.
Print Assumptions memory_array_separation_exact.
Print Assumptions memory_registry_instruction_backend.
Print Assumptions compile_memory_registry_loop_correct.
Print Assumptions memory_instruction_registry_transfer.
Print Assumptions memory_cross_update_evaluation.
Print Assumptions memory_cross_update_inverse.
Print Assumptions memory_cross_registry_execution.
Print Assumptions memory_copy_statement_evaluation.
Print Assumptions memory_copy_statement_inverse.
Print Assumptions memory_copy_registry_execution.
Print Assumptions named_operation_registry_execution.
Print Assumptions named_array_operations_source_clight_iterations.
Print Assumptions named_array_operations_registry.
Print Assumptions memory_registry_guard_primitives.
Print Assumptions named_array_operations_source_clight_decode.
Print Assumptions memory_named_guard_primitives.
Print Assumptions frontend_variable_settle_decode.
Print Assumptions memory_ragged_sequence_lift.
Print Assumptions memory_ragged_source_decode.
Print Assumptions memory_ragged_source_guard_domain.
Print Assumptions named_array_operations_ragged_source_decode.
Print Assumptions memory_ragged_width_exact.
Print Assumptions memory_ragged_guard_primitives.
Print Assumptions memory_ragged_parameter_bounds.
Print Assumptions memory_ragged_tile_trimming.
Print Assumptions memory_named_array_candidate_rule.
Print Assumptions memory_source_affine_evaluation.
Print Assumptions memory_source_affine_defined_words.
Print Assumptions memory_source_affine_decode.
Print Assumptions memory_source_affine_row_extrema.
Print Assumptions memory_source_affine_iteration_value.
Print Assumptions memory_source_loop_expression_value.
Print Assumptions memory_source_context_typed.
Print Assumptions memory_source_endpoints_sound.
Print Assumptions memory_parametric_source_decode.
Print Assumptions memory_parametric_source_words.
Print Assumptions memory_parametric_sequence_lift.
Print Assumptions named_array_operations_parametric_source_decode.
Print Assumptions compile_memory_source_width_sound.
Print Assumptions memory_parametric_restore_execution.
Print Assumptions memory_source_guard_primitives.
Print Assumptions memory_parametric_named_source_domain.
Print Assumptions memory_parametric_tile_trimming.
Print Assumptions memory_parametric_array_candidate_rule.
Print Assumptions memory_common_layout_facts.
Print Assumptions memory_common_layout_points.
Print Assumptions memory_layout_copy_statement_evaluation.
Print Assumptions memory_layout_copy_statement_inverse.
Print Assumptions memory_layout_copy_registry_execution.
Print Assumptions memory_layout_copy_registry.
Print Assumptions memory_layout_copy_point_execution.
Print Assumptions memory_copy_layout_registry.
Print Assumptions memory_copy_layout_point_execution.
Print Assumptions memory_parametric_body_source_decode.
Print Assumptions memory_named_body_model.
Print Assumptions memory_layout_copy_body_model.
Print Assumptions memory_descriptor_entries_exist.
Print Assumptions memory_layout_copy_general_registry_point.
Print Assumptions memory_layout_operation_clight_inverse.
Print Assumptions memory_layout_operation_registry_execution.
Print Assumptions memory_layout_sequence_registry.
Print Assumptions memory_layout_sequence_point_execution.
Print Assumptions memory_layout_body_model.
Print Assumptions memory_index_expression_evaluation.
Print Assumptions memory_affine_access_load_inverse.
Print Assumptions memory_affine_access_registry.
Print Assumptions memory_affine_copy_inverse.
Print Assumptions memory_affine_copy_registry_point.
Print Assumptions memory_general_layout_registry_execution.
Print Assumptions memory_general_sequence_registry.
Print Assumptions memory_general_sequence_point_execution.
Print Assumptions memory_general_layout_body_model.
Print Assumptions memory_general_anchors_registry.
Print Assumptions memory_index_offset_box_sound.
Print Assumptions memory_offset_sequence_point_execution.
Print Assumptions memory_offset_layout_body_model.
Print Assumptions check_memory_offset_region.
Print Assumptions memory_source_value_loads_exist.
Print Assumptions memory_source_value_evaluation_inverse.
Print Assumptions memory_affine_reads_resolve.
Print Assumptions memory_affine_reads_loads.
Print Assumptions memory_affine_compute_inverse.
Print Assumptions memory_affine_compute_registry.
Print Assumptions memory_compute_anchor_bindings.
Print Assumptions memory_compute_sequence_registry.
Print Assumptions memory_compute_sequence_point_execution.
Print Assumptions memory_compute_body_model.
Print Assumptions check_memory_compute_region.
Print Assumptions memory_parametric_body_restrict.
Print Assumptions memory_parametric_package_restrict.
Print Assumptions check_memory_parametric_with_widths_sound.
Print Assumptions memory_parametric_body_source_domain.
Print Assumptions memory_parametric_body_candidate_rule.
Print Assumptions memory_layout_copy_source_decode.
Print Assumptions memory_layout_copy_source_domain.
Print Assumptions memory_layout_copy_candidate_rule.
Print Assumptions MemoryFramedNested.compile_nested_correct.
Print Assumptions memory_recursive_source_decode_framed.
Print Assumptions memory_recursive_first_leaf.
Print Assumptions memory_pointer_lvalue_inverse.
Print Assumptions memory_pointer_load_inverse.
Print Assumptions memory_source_value_inverse.
Print Assumptions memory_pointer_instruction_backend.
Print Assumptions compile_memory_pointer_buffer_loop_correct.
Print Assumptions memory_pointer_compute_inverse.
Print Assumptions memory_pointer_compute_registry.
Print Assumptions memory_pointer_sequence_tail_inverse.
Print Assumptions memory_pointer_sequence_point_execution.
Print Assumptions check_memory_pointer_region.
Print Assumptions memory_pointer_source_first_base.
Print Assumptions memory_pointer_body_source_decode.
Print Assumptions memory_pointer_region_source_domain.
Print Assumptions check_memory_pointer_caps_sound.
Print Assumptions memory_pad_access_cell.
Print Assumptions memory_pad_sequence_point.
Print Assumptions memory_scalar_arguments_value.
Print Assumptions memory_scalar_rectangle_iterations.
Print Assumptions memory_source_parameter_inverse.
Print Assumptions memory_source_used_register_typed.
Print Assumptions memory_scalar_rectangle_lift.
Print Assumptions memory_scalar_access_cell.
Print Assumptions memory_scalar_pointer_access_registry.
Print Assumptions memory_scalar_pointer_compute_inverse.
Print Assumptions memory_scalar_pointer_used_register.
Print Assumptions memory_scalar_pointer_compute_registry.
Print Assumptions memory_scalar_pointer_compute_check_sound.
Print Assumptions memory_scalar_pointer_registers_check_sound.
Print Assumptions memory_scalar_pointer_sequence_tail_inverse.
Print Assumptions memory_scalar_pointer_sequence_point_execution.
Print Assumptions memory_scalar_pointer_sequence_used_register.
Print Assumptions check_memory_scalar_pointer_region.
Print Assumptions memory_scalar_pointer_source_first_capability.
Print Assumptions memory_scalar_pointer_body_source_decode.
Print Assumptions memory_scalar_pointer_source_under_ranges.
Print Assumptions memory_scalar_pointer_region_source_domain.
Print Assumptions memory_scalar_validator_count_scalar_ranges.
Print Assumptions memory_scalar_encoder_count_scalar_ranges.
Print Assumptions memory_carry_scalar_arguments.
Print Assumptions check_memory_scalar_pointer_caps_sound.
Print Assumptions memory_scalar_array_compute_inverse.
Print Assumptions memory_scalar_array_used_register.
Print Assumptions memory_scalar_array_compute_check_sound.
Print Assumptions memory_scalar_array_sequence_tail_inverse.
Print Assumptions memory_scalar_array_sequence_used_register.
Print Assumptions memory_scalar_array_sequence_point_execution.
Print Assumptions memory_scalar_array_sequence_registry.
Print Assumptions check_memory_scalar_array_region.
Print Assumptions memory_scalar_array_source_first_capability.
Print Assumptions memory_scalar_array_body_source_decode.
Print Assumptions memory_scalar_array_source_under_ranges.
Print Assumptions memory_scalar_array_region_source_domain.
Print Assumptions check_memory_scalar_array_caps_sound.
Print Assumptions memory_pointer_cells_comparison.
Print Assumptions memory_pointer_cells_unequal_separated.
Print Assumptions memory_restrict_instruction_semantics.
Print Assumptions memory_unrestrict_loop_execution.
Print Assumptions memory_event_access_capabilities.
Print Assumptions memory_loop_source_capabilities.
Print Assumptions memory_multi_pointer_locations_int32.
Print Assumptions memory_multi_pointer_cell_encoding.
Print Assumptions memory_multi_pointer_compute_inverse.
Print Assumptions memory_multi_pointer_compute_registry.
Print Assumptions memory_multi_pointer_sequence_point_execution.
Print Assumptions memory_multi_pointer_body_source_decode.
Print Assumptions memory_multi_pointer_source_under_ranges.
Print Assumptions compile_memory_multi_pointer_buffer_loop_correct.
Print Assumptions memory_coordinate_activation_exact.
Print Assumptions memory_coordinate_activation_semantics.
Print Assumptions memory_scalar_rectangle_footprint.
Print Assumptions memory_rectangular_selected_members.
Print Assumptions memory_multi_pointer_selected_footprint.
Print Assumptions memory_multi_pointer_region_source_guard_domain.
Print Assumptions memory_multi_pointer_region_guard_exact.
Print Assumptions memory_multi_pointer_region_guard_nonalias.
Print Assumptions memory_multi_pointer_region_guard_primitives.
Print Assumptions memory_private_rule_sequential_sound.
Print Assumptions memory_compact_alias_statement_execution.
Print Assumptions memory_multi_pointer_region_guard_statement_execution.
Print Assumptions memory_boolean_scan_loop.
Print Assumptions memory_pointer_range_pair_execution.
Print Assumptions memory_linear_pointer_runtime_footprint.
Print Assumptions memory_linear_pointer_pair_separation.
Print Assumptions memory_linear_pointer_guard_execution.
Goal True. idtac "MEM_ADAPTED_VALIDATOR". exact I. Qed.
Print Assumptions guarded_memory_validate_refines.
Print Assumptions guarded_memory_validate_tiling_refines.
Print Assumptions guarded_memory_checked_tiling_refines.
Print Assumptions validated_memory_equivalence.
Print Assumptions validated_memory_equivalence_at.
Print Assumptions validated_memory_rectangle_interchange.
Print Assumptions before_to_retiled_old_progress.
Print Assumptions validated_memory_single_tiling_progress_at.
Print Assumptions guarded_memory_tiling_equivalence_refines.
Print Assumptions validated_memory_rectangle_tiling.
Print Assumptions validated_memory_cut_tiling.
Print Assumptions before_to_retiled_multiple_progress.
Print Assumptions validated_memory_multiple_tiling_progress_at.
Print Assumptions validated_memory_sequence_tiling.
Print Assumptions validated_memory_affine_loops_at.
Print Assumptions validated_memory_reindexed_loops_at.
Print Assumptions validated_memory_equivalent_domain_loops_at.
Print Assumptions memory_check_domain_equivalence_correct.
Print Assumptions memory_aligned_domains_execution.
Print Assumptions checked_named_affine_candidate_correct.
Print Assumptions validated_memory_affine_mapped_domain_loops_at.
Print Assumptions checked_named_mapped_candidate_correct.
Print Assumptions checked_named_ragged_candidate_correct.
Print Assumptions validated_memory_extracted_tiling_loops_at.
Print Assumptions checked_named_ragged_tiling_correct.
Print Assumptions memory_attempt_codegen_accept.
Print Assumptions memory_checked_generated_loop_certificate.
Print Assumptions checked_named_tiled_candidate_correct.
Print Assumptions checked_named_parametric_candidate_correct.
Print Assumptions checked_named_parametric_tiling_correct.
Print Assumptions checked_parametric_instruction_candidate_correct.
Print Assumptions checked_parametric_instruction_tiling_correct.
Print Assumptions checked_memory_scalar_candidate_correct.
Print Assumptions checked_memory_scalar_tiling_correct.
Goal True. idtac "MEM_REGION". exact I. Qed.
Print Assumptions memory_validated_rectangle_local.
Print Assumptions memory_validated_rectangle_rule.
Print Assumptions check_memory_region_sound.
Print Assumptions memory_tiled_rectangle_local.
Print Assumptions memory_tiled_rectangle_rule.
Print Assumptions check_memory_tiled_region_sound.
Print Assumptions memory_cut_tiled_local.
Print Assumptions check_memory_cut_region_sound.
Print Assumptions memory_tiled_array_family_local.
Print Assumptions memory_mode_tiled_rectangle_local.
Print Assumptions check_memory_sequence_region_sound.
Print Assumptions memory_tiled_array_operations_local.
Print Assumptions check_memory_operations_region_sound.
Print Assumptions memory_proposed_array_operations_local.
Print Assumptions check_memory_proposed_region_sound.
Print Assumptions check_memory_unified_region_sound.
Print Assumptions check_memory_named_affine_region_sound.
Print Assumptions check_memory_named_mapped_region_sound.
Print Assumptions check_memory_named_tiled_region_sound.
Print Assumptions check_memory_named_unified_region_sound.
Print Assumptions memory_ragged_array_candidate_local.
Print Assumptions memory_ragged_named_source_domain.
Print Assumptions memory_ragged_array_candidate_rule.
Print Assumptions check_memory_ragged_mapped_region_sound.
Print Assumptions check_memory_ragged_tiled_region_sound.
Print Assumptions check_memory_ragged_scheduled_region_sound.
Print Assumptions check_memory_named_scheduled_region_sound.
Print Assumptions check_memory_ragged_unified_region_sound.
Print Assumptions check_memory_parametric_mapped_region_sound.
Print Assumptions check_memory_parametric_scheduled_region_sound.
Print Assumptions check_memory_parametric_tiled_region_sound.
Print Assumptions check_memory_parametric_unified_region_sound.
Print Assumptions check_memory_layout_copy_mapped_region_sound.
Print Assumptions check_memory_layout_copy_scheduled_region_sound.
Print Assumptions check_memory_layout_copy_tiled_region_sound.
Print Assumptions check_memory_layout_copy_unified_region_sound.
Print Assumptions check_memory_parametric_region_mapped_sound.
Print Assumptions check_memory_parametric_region_conditioned_sound.
Print Assumptions check_memory_parametric_region_scheduled_sound.
Print Assumptions check_memory_parametric_region_conditioned_tiling_sound.
Print Assumptions memory_nary_box_sound.
Print Assumptions memory_signed_box_sound.
Print Assumptions memory_signed_box_accepts_nonnegative.
Print Assumptions memory_nary_access_check_sound.
Print Assumptions memory_nary_compute_inverse.
Print Assumptions memory_nary_compute_sequence_point_execution.
Print Assumptions memory_nary_compute_body_model.
Print Assumptions memory_nary_rectangle_lift.
Print Assumptions memory_recursive_source_decode.
Print Assumptions memory_recursive_body_source_decode.
Print Assumptions check_memory_recursive_region.
Print Assumptions memory_recursive_guard_exact.
Print Assumptions memory_recursive_source_bound_words.
Print Assumptions memory_recursive_region_source_domain.
Print Assumptions memory_recursive_restore_execution.
Print Assumptions checked_memory_recursive_candidate_correct.
Print Assumptions checked_memory_recursive_tiling_correct.
Print Assumptions memory_recursive_candidate_local.
Print Assumptions check_memory_recursive_mapped_region_sound.
Print Assumptions check_memory_recursive_tiled_region_sound.
Print Assumptions check_memory_recursive_scheduled_region_sound.
Print Assumptions check_memory_recursive_unified_region_sound.
Print Assumptions memory_triple_source_decode.
Print Assumptions memory_triple_source_words.
Print Assumptions memory_triple_body_source_decode.
Print Assumptions memory_triple_guard_exact.
Print Assumptions memory_triple_region_source_domain.
Print Assumptions checked_memory_triple_candidate_correct.
Print Assumptions checked_memory_triple_tiling_correct.
Print Assumptions memory_triple_candidate_local.
Print Assumptions check_memory_triple_mapped_region_sound.
Print Assumptions check_memory_triple_tiled_region_sound.
Print Assumptions check_memory_triple_scheduled_region_sound.
Print Assumptions memory_pointer_candidate_local.
Print Assumptions memory_pointer_candidate_rule.
Print Assumptions memory_pointer_region_target_sound.
Print Assumptions check_memory_pointer_region_candidate_sound.
Print Assumptions check_memory_pointer_mapped_region_sound.
Print Assumptions check_memory_pointer_tiled_region_sound.
Print Assumptions check_memory_pointer_scheduled_region_sound.
Print Assumptions check_memory_pointer_unified_region_sound.
Print Assumptions memory_scalar_pointer_candidate_local.
Print Assumptions memory_scalar_pointer_candidate_rule.
Print Assumptions check_memory_scalar_pointer_mapped_region_sound.
Print Assumptions check_memory_scalar_pointer_tiled_region_sound.
Print Assumptions check_memory_scalar_pointer_scheduled_region_sound.
Print Assumptions check_memory_scalar_pointer_unified_region_sound.
Print Assumptions memory_scalar_array_candidate_local.
Print Assumptions memory_scalar_array_candidate_rule.
Print Assumptions check_memory_scalar_array_mapped_region_sound.
Print Assumptions check_memory_scalar_array_tiled_region_sound.
Print Assumptions check_memory_scalar_array_scheduled_region_sound.
Print Assumptions check_memory_scalar_array_unified_region_sound.
Print Assumptions memory_finite_footprint_separated_candidate.
Print Assumptions memory_multi_pointer_candidate_local.
Print Assumptions memory_multi_pointer_candidate_rule.
Print Assumptions check_memory_multi_pointer_mapped_region_sound.
Print Assumptions check_memory_multi_pointer_tiled_region_sound.
Print Assumptions check_memory_multi_pointer_scheduled_region_sound.
Print Assumptions check_memory_multi_pointer_unified_region_sound.
Print Assumptions memory_projected_private_rule_sound.
Print Assumptions memory_private_rule_projected_check_sound.
Print Assumptions memory_multi_pointer_projected_candidate_rule.
Print Assumptions check_memory_linear_pointer_mapped_package_sound.
Print Assumptions check_memory_linear_pointer_scheduled_package_sound.
Print Assumptions check_memory_linear_pointer_unified_region_sound.
Print Assumptions memory_stateful_clight_language.
Print Assumptions memory_stateful_clight_sequence.
Print Assumptions memory_projected_private_rule_stateful_sound.
Print Assumptions memory_source_affine_rename_evaluation.
Print Assumptions memory_affine_range_address_binding.
Print Assumptions memory_affine_range_pair_execution.
Print Assumptions memory_affine_endpoint_pair_execution.
Print Assumptions memory_affine_pair_choice_execution.
Print Assumptions memory_affine_pointer_runtime_footprint.
Print Assumptions memory_affine_pointer_accesses_encoding.
Print Assumptions memory_affine_pointer_pairs_separation.
Print Assumptions memory_affine_access_pairs_execution.
Print Assumptions memory_affine_pointer_guard_execution.
Print Assumptions check_memory_affine_pointer_mapped_package_sound.
Print Assumptions check_memory_affine_pointer_scheduled_package_sound.
Print Assumptions memory_boolean_rectangle_execution.
Print Assumptions memory_affine_axis_repeated_renamed_evaluation.
Print Assumptions memory_affine_axis_repeated_address_binding.
Print Assumptions memory_affine_axis_boundary_test_evaluation.
Print Assumptions memory_affine_axis_boundary_mask_execution.
Print Assumptions memory_affine_axis_boundary_masks_execution.
Print Assumptions memory_affine_axis_boundary_pair_execution.
Print Assumptions memory_affine_axis_pair_choice_execution.
Print Assumptions memory_affine_axis_renamed_evaluation.
Print Assumptions memory_affine_axis_address_binding.
Print Assumptions memory_affine_axis_pair_execution.
Print Assumptions memory_axis_pointer_pairs_separation.
Print Assumptions memory_axis_access_pairs_execution.
Print Assumptions memory_axis_pointer_guard_execution.
Print Assumptions check_memory_axis_pointer_mapped_package_sound.
Print Assumptions check_memory_axis_pointer_scheduled_package_sound.
Print Assumptions check_memory_axis_pointer_tiled_package_sound.
Print Assumptions check_memory_axis_pointer_caps_sound.
Print Assumptions check_memory_affine_pointer_unified_region_sound.
Print Assumptions memory_vector_source_bound_words.
Print Assumptions memory_vector_bounds_exact.
Print Assumptions memory_vector_guard_exact.
Print Assumptions check_memory_vector_pointer_region.
Print Assumptions memory_vector_pointer_source_first_capability.
Print Assumptions memory_vector_pointer_body_source_decode.
Print Assumptions memory_vector_pointer_source_under_ranges.
Print Assumptions memory_vector_pointer_region_source_domain.
Print Assumptions memory_vector_pointer_source_runtime_domain.
Print Assumptions memory_vector_pointer_projected_candidate_rule.
Print Assumptions checked_memory_bounded_candidate_correct.
Print Assumptions checked_memory_bounded_tiling_correct.
Print Assumptions memory_vector_axis_access_pairs_execution.
Print Assumptions memory_vector_axis_pointer_guard_execution.
Print Assumptions check_memory_vector_axis_pointer_region_candidate_sound.
Print Assumptions check_memory_vector_axis_pointer_mapped_package_sound.
Print Assumptions check_memory_vector_axis_pointer_scheduled_package_sound.
Print Assumptions check_memory_vector_axis_pointer_tiled_package_sound.
Print Assumptions check_memory_vector_axis_profiles_sound.
Print Assumptions check_memory_vector_axis_unified_region_sound.
Print Assumptions memory_pointer_lvalue_index_word.
Print Assumptions memory_pointer_source_affine_used_word.
Print Assumptions memory_pointer_operation_address_words.
Print Assumptions memory_pointer_sequence_address_words.
Print Assumptions memory_parameter_range_exact.
Print Assumptions memory_parameter_ranges_exact.
Print Assumptions memory_param_pointer_source_first_capability.
Print Assumptions memory_param_pointer_body_source_decode.
Print Assumptions memory_param_pointer_source_under_ranges.
Print Assumptions memory_param_pointer_region_source_domain.
Print Assumptions memory_param_pointer_header_exact.
Print Assumptions memory_param_pointer_header_sound.
Print Assumptions memory_param_pointer_source_header_domain.
Print Assumptions memory_param_pointer_source_runtime_domain.
Print Assumptions memory_param_pointer_projected_candidate_rule.
Print Assumptions memory_param_pointer_source_footprint.
Print Assumptions memory_param_axis_pointer_runtime_footprint.
Print Assumptions memory_param_axis_pointer_pairs_separation.
Print Assumptions memory_param_affine_axis_boundary_test_evaluation.
Print Assumptions memory_param_affine_axis_boundary_mask_execution.
Print Assumptions memory_param_affine_axis_boundary_masks_execution.
Print Assumptions memory_param_affine_axis_boundary_pair_execution.
Print Assumptions memory_param_affine_axis_pair_choice_execution.
Print Assumptions memory_param_affine_axis_pair_execution.
Print Assumptions memory_param_axis_access_pairs_execution.
Print Assumptions memory_param_axis_pointer_guard_execution.
Print Assumptions check_memory_param_axis_pointer_region_candidate_sound.
Print Assumptions check_memory_param_axis_pointer_mapped_package_sound.
Print Assumptions check_memory_param_axis_pointer_scheduled_package_sound.
Print Assumptions check_memory_param_axis_pointer_tiled_package_sound.
Print Assumptions check_memory_param_axis_profiles_sound.
Print Assumptions check_memory_param_axis_unified_region_sound.
Print Assumptions memory_projected_verified_version.
Print Assumptions memory_version_family_sound.
Print Assumptions memory_version_components_sound.
Print Assumptions memory_version_components_nonempty_sound.
Print Assumptions memory_param_axis_pointer_components_valid.
Print Assumptions check_memory_param_axis_pointer_region_components_sound.
Print Assumptions check_memory_param_axis_pointer_mapped_package_components_sound.
Print Assumptions check_memory_param_axis_pointer_scheduled_package_components_sound.
Print Assumptions check_memory_param_axis_pointer_tiled_package_components_sound.
Print Assumptions collect_memory_param_version_groups_sound.
Print Assumptions compile_memory_param_version_groups_sound.
Print Assumptions check_memory_param_version_unified_region_sound.
Print Assumptions memory_check_tree_parse_sound.
Print Assumptions memory_check_tree_decode.
Print Assumptions memory_projected_tree_prefix.
Print Assumptions memory_verified_guarded_rule.
Print Assumptions memory_prefilter_components_valid.
Print Assumptions memory_prefilter_component_list_sound.
Print Assumptions compile_memory_param_prefilter_groups_sound.
Print Assumptions check_memory_param_prefilter_unified_region_sound.
Goal True. idtac "MEM_COMPILER". exact I. Qed.
Print Assumptions compile_memory_regions_correct.
Print Assumptions compile_memory_tiled_regions_correct.
Print Assumptions compile_memory_cut_regions_correct.
Print Assumptions compile_memory_sequence_regions_correct.
Print Assumptions compile_memory_operations_regions_correct.
Print Assumptions compile_memory_proposed_regions_correct.
Print Assumptions compile_memory_unified_regions_correct.
Goal True. idtac "MEM_END". exact I. Qed.
""")
    result = subprocess.run(["rocq", "compile", *flags, str(audit)], cwd=ROOT, check=True,
                            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (WORK / "audit.log").write_text(result.stdout)
    cc, rest = result.stdout.split("MEM_CC_BASE", 1)[1].split("MEM_VALIDATOR_BASE", 1)
    baseline, rest = rest.split("MEM_STATEFUL_CORE", 1)
    stateful_core, rest = rest.split("MEM_AFFINE_GUARD_MATH", 1)
    affine_guard_math, rest = rest.split("MEM_PHYSICAL_REGISTRY", 1)
    registry, rest = rest.split("MEM_INSTRUCTION", 1)
    instruction, rest = rest.split("MEM_ADAPTED_VALIDATOR", 1)
    adapted, rest = rest.split("MEM_REGION", 1)
    region, rest = rest.split("MEM_COMPILER", 1)
    compiler = rest.split("MEM_END", 1)[0]
    if names(stateful_core) or "Closed under the global context" not in stateful_core:
        raise SystemExit("unexpected abstract stateful core assumptions")
    if names(affine_guard_math) or "Closed under the global context" not in affine_guard_math:
        raise SystemExit("unexpected affine guard strategy assumptions")
    if names(registry) or "Closed under the global context" not in registry:
        raise SystemExit("unexpected physical-registry assumptions")
    if names(instruction) - names(cc) or names(adapted) != names(baseline):
        raise SystemExit("concrete memory adapter adds unexpected global assumptions")
    expected = names(cc) | names(baseline)
    if names(region) - expected or names(compiler) != expected:
        raise SystemExit("memory compiler differs from the CompCert and concrete validator union")
    sources = [DIRECTORY / (module + ".v") for module in MODULES]
    sources += sorted((ROOT / "theories").glob("*.v"))
    result = {
        "status": "compiled", "checked_modules": MODULES, "checked_lowering_modules": LOWERING_MODULES,
        "checked_stateful_core_modules": STATEFUL_CORE_MODULES,
        "stateful_core_global_axioms": [],
        "stateful_core_instantiated_in_clight_projected_region_contract": True,
        "stateful_version_families_proved": True,
        "memory_parameter_version_families_csem_asm_proved": True,
        "memory_guard_prefilter_csem_asm_proved": True,
        "memory_guard_prefilter_scope": "opt-in prefilter versions per-axis template; recognize a decision-tree prefix of a certified stateful check; derive defined execution and unchanged registers/memory from the original encoding; prefix refusal tries the next version, prefix acceptance executes the original guarded candidate including its source fallback; preserves source observations for arbitrary certified components, no general acceptance or cost guarantee",
        "memory_parameter_version_families_scope": "opt-in versions per-axis candidate template; finite heterogeneous abstract guard versions share source observations but may have different domains, presumptions and frames; actual Clight check/candidate components certified from checked source packages and real candidate certificates; first statically validated profile in each address-cap group 64,16,8,4,1; sequential runtime choice and final original-source fallback; mapped, scheduled and outer-two-axis tiling candidates; no weakest-condition or optimal-box guarantee, no shared alias-result cache",
        "affine_loop_alias_guard_clight_execution_proved": True,
        "affine_loop_alias_guard_csem_asm_route_proved": True,
        "affine_loop_alias_guard_raw_access_limit": 32,
        "affine_pair_strategy_math_global_axioms": [],
        "affine_loop_alias_guard_linear_strategy_proved": True,
        "affine_loop_alias_guard_linear_strategy_scope": "equal affine slopes or either affine slope zero; one private counted loop with two source-derived endpoint comparisons per cross-pointer access pair; arbitrary signed slopes and modular pointer offsets",
        "multi_axis_loop_alias_guard_proved": True,
        "multi_axis_loop_alias_guard_csem_asm_route_proved": True,
        "multi_axis_per_axis_bounds_source_and_guard_proved": True,
        "multi_axis_per_axis_bounds_candidate_and_lowering_proved": True,
        "multi_axis_per_axis_bounds_csem_asm_proved": True,
        "pointer_affine_address_parameter_boundary_scans_proved": True,
        "pointer_affine_address_parameter_boundary_scans_csem_asm_proved": True,
        "pointer_affine_address_parameter_boundary_scans_scope": "fixed actual address parameters; boundary masks over active coordinate axes only; compare coordinate coefficient prefixes, allowing different parameter coefficients; exact full-check equivalence under source-derived physical capabilities; 2^d P for equal coordinate coefficients and full P^2 otherwise; same cap profiles, candidates and whole-program contract; no unconditional speedup or raw-pair deduplication",
        "pointer_affine_address_parameters_source_and_guard_proved": True,
        "pointer_affine_address_parameters_candidate_and_lowering_proved": True,
        "pointer_affine_address_parameters_csem_asm_proved": True,
        "pointer_affine_address_parameters_scope": "opt-in per-axis candidate template; one or more canonical rectangular axes; one or more stable signed address temporaries with checked nonnegative finite intervals; independent source package checks, source-derived conditional word types and physical cells; private scans retain fixed parameter values and iterate only active coordinates; mapped and scheduled candidates and outer-two-axis tiling; full signed RHS scalars remain separate; finite parameter cap profiles and greedy axis caps; no allocation extent assumption; boundary scans for equal coordinate coefficient prefixes, full pair scans otherwise; no parameterized strides or negative address parameter fast path",
        "multi_axis_per_axis_bounds_scope": "opt-in per-axis candidate template; canonical rectangular counted pointer sources; individually checked positive signed caps, greedy source-access box proposal and finite single-axis tightening; actual source-derived word/read/write capabilities, short-circuit check encoding, stable RHS scalars, mapped and scheduled candidates and outer-two-axis tiling; no logical-window allocation assumption",
        "multi_axis_loop_alias_guard_boundary_strategy_proved": True,
        "multi_axis_loop_alias_guard_boundary_strategy_scope": "equal full affine coefficient vectors; modular physical-pointer offsets; static Boolean masks and one private active-rectangle scan per mask, using source-capable boundary coordinates; exactly the previous full-pair Boolean result under source capabilities; 2^d times P comparisons per raw cross-pointer access pair; other coefficient vectors retain the quadratic scan",
        "multi_axis_loop_alias_guard_scope": "any finite canonical rectangular counted nest, independent signed32 bounds including shared bound identifiers; signed affine source-coordinate pointer addresses; two private counter vectors and one flag; all cross-pointer access pairs scanned over the active source rectangle; raw-access budget 32, logical window 1024, certified cap search [1024,64,32,16,8,4,1]; mapped, generated-schedule and two-dimensional tiling candidates; equal coefficient vectors use 2^d boundary rectangles times active points; other pairs remain quadratic in the number of active points",

        "affine_loop_alias_guard_scope": "one canonical counted axis, any finite set of accessed pointer identifiers and signed affine coordinate expressions, finite read/write operation lists and stable RHS scalars; actual source-derived valid aligned addresses; all cross-pointer access pairs scanned with three private temporaries; cap derived from logical window 1024 and checked address ranges; mapped and generated-schedule candidates",
        "physical_flat_array_nonalias_global_axioms": [],
        "instruction_assumptions": sorted(names(instruction)),
        "actual_validator_baseline_assumptions": sorted(names(baseline)),
        "concrete_validator_assumptions": sorted(names(adapted)),
        "memory_region_assumptions": sorted(names(region)),
        "whole_program_assumptions": sorted(names(compiler)),
        "whole_program_entrypoint": "GuardMemoryCompiler.compile_memory_regions",
        "whole_program_theorem": "GuardMemoryCompiler.compile_memory_regions_correct",
        "cut_whole_program_entrypoint": "GuardMemoryCutCompiler.compile_memory_cut_regions",
        "cut_whole_program_theorem": "GuardMemoryCutCompiler.compile_memory_cut_regions_correct",
        "tiling_whole_program_entrypoint": "GuardMemoryTiledCompiler.compile_memory_tiled_regions",
        "tiling_whole_program_theorem": "GuardMemoryTiledCompiler.compile_memory_tiled_regions_correct",
        "sequence_whole_program_entrypoint": "GuardMemorySequenceCompiler.compile_memory_sequence_regions",
        "sequence_whole_program_theorem": "GuardMemorySequenceCompiler.compile_memory_sequence_regions_correct",
        "operations_whole_program_entrypoint": "GuardMemoryOperationsCompiler.compile_memory_operations_regions",
        "operations_whole_program_theorem": "GuardMemoryOperationsCompiler.compile_memory_operations_regions_correct",
        "proposed_whole_program_entrypoint": "GuardMemoryProposedCompiler.compile_memory_proposed_regions",
        "proposed_whole_program_theorem": "GuardMemoryProposedCompiler.compile_memory_proposed_regions_correct",
        "unified_whole_program_entrypoint": "GuardMemoryUnifiedCompiler.compile_memory_unified_regions",
        "unified_whole_program_theorem": "GuardMemoryUnifiedCompiler.compile_memory_unified_regions_correct",
        "one_guarded_compiler_for_affine_and_tiling_candidates_proved": True,
        "multiple_physical_arrays_registry_nonalias_closed": True,
        "array_object_base_guard_encoding_proved": True,
        "multiarray_actual_source_and_candidate_clight_bridge_proved": True,
        "multiarray_unified_csem_asm_proved": True,
        "multiarray_c_source_scope": "rectangular pure-write, own-cell and row-prefix statements on distinct actual array objects sharing a fixed layout; cross-array reads and pointer slices are not decoded",
        "untrusted_loop_candidate_csem_asm_proved": True,
        "untrusted_loop_candidate_c_source_scope": "canonical rectangular mixed statements on one fixed-layout array",
        "multiple_mixed_array_statements_tiling_csem_asm_proved": True,
        "operations_c_source_scope": "nonempty list of pure writes, own-cell updates and row-prefix updates on one fixed-layout array",
        "multiple_pure_array_statements_tiling_csem_asm_proved": True,
        "sequence_c_source_scope": "nonempty pure-write statement list on one fixed-layout array",
        "whole_program_acceptance": "alarm-free mayReturn with OK assembly program",
        "additional_global_axioms": [],
        "concrete_instr_module": "GuardMemoryInstr.GuardMemoryInstr",
        "actual_compcert_mem_load_store_execution": True,
        "state_equivalence": "exact registry and Mem equality",
        "instruction_interface_fields_are_proved": True,
        "cstate_valid_used": False,
        "affine_access_footprints_checked": True,
        "pure_payload_operations": ["constant", "parameter", "loaded value", "Int.add", "Int.sub", "Int.mul"],
        "actual_clight_store_to_instr_decoder_instantiated": True,
        "actual_affine_and_tiling_validator_instantiated": True,
        "actual_point_space_tiling_checker_instantiated": True,
        "bidirectional_affine_validation_establishes_progress": True,
        "single_statement_tiling_source_to_candidate_progress_proved": True,
        "tiling_progress_preserves_actual_parameters": True,
        "general_multiple_statement_tiling_progress_proved": True,
        "native_validator_validation_report": "build/native-memory-validator/report.json",
        "canonical_rectangle_clight_to_loop_decoder_instantiated": True,
        "canonical_rectangle_loop_to_clight_encoder_instantiated": True,
        "general_pure_array_loop_to_clight_encoder_instantiated": True,
        "general_single_flat_array_memory_loop_encoder_instantiated": True,
        "flat_array_encoder_payload_operations": ["constant", "parameter", "loaded value", "Int.add", "Int.sub", "Int.mul"],
        "read_modify_write_rectangle_tiling_csem_asm_proved": True,
        "row_prefix_read_rectangle_tiling_csem_asm_proved": True,
        "nonnegative_floor_division_lowering_proved": True,
        "pure_rectangle_two_dimensional_tiling_csem_asm_proved": True,
        "affine_conditional_domain_two_dimensional_tiling_csem_asm_proved": True,
        "conditional_domain_c_source_scope": "one static affine leaf cut with nonnegative limit",
        "pure_rectangle_tiling_public_exit": "agreement on all source program temporaries and exact Mem",
        "pure_rectangle_tiling_partial_tiles_checked": True,
        "canonical_rectangle_memory_modes": ["pure write", "own-cell update", "row-prefix update"],
        "canonical_rectangle_public_exit": "exact full temporary environment and Mem",
        "canonical_rectangle_clight_poly_bridge_instantiated": True,
        "canonical_rectangle_dependence_csem_asm_rule_instantiated": True,
        "polyhedral_parameters_preserved_by_validator": True,
        "complete_source_loop_decoder_instantiated": False,
        "complete_candidate_loop_encoder_instantiated": False,
        "complete_csem_asm_rule_instantiated": False,
        "general_affine_loop_to_poly_execution_equivalence_proved": True,
        "general_loop_statement_scope": "arbitrary nesting of affine Loop, Seq and conjunctive affine Guard accepted by the actual extractor",
        "semantically_equivalent_affine_domain_alignment_proved": True,
        "domain_equivalence_uses_existing_emptiness_certificates": True,
        "adjacent_iterator_coordinate_permutation_proved": True,
        "externally_proposed_iterator_coordinate_swaps_consumed": True,
        "domain_constraint_order_normalization_proved": True,
        "point_representation_isomorphism_semantic_interface_proved": True,
        "array_entry_presumption_consumed_by_candidate_checker": True,
        "general_affine_loop_candidate_equivalence_checker": "GuardMemoryExtractorProgress.checked_memory_loop_equivalence",
        "general_affine_loop_progress_theorem": "GuardMemoryExtractorProgress.validated_memory_affine_loops_at",
        "general_loop_endpoint_preserves_exact_entry_parameters_and_mem": True,
        "general_loop_endpoint_is_complete_c_source_decoder": False,
        "external_scheduler_connected": False,
        "different_array_layout_copy_c_bridge_proved": True,
        "different_array_layout_guard_machine_encoding_proved": True,
        "different_array_layout_source_scope": "one signed-int copy between named arrays with independently fixed extents and strides, including same-array remapping with equal extents, parametric affine inner bound, and conservative common row/column guard",
        "same_array_different_stride_copy_registry_proved": True,
        "same_array_copy_actual_dependence_validation_proved": True,
        "parametric_source_body_semantic_interface_instantiated": True,
        "heterogeneous_layout_operation_list_c_bridge_proved": True,
        "anchored_nonzero_affine_c_accesses_proved": True,
        "affine_multi_read_value_computations_proved": True,
        "affine_multi_read_value_computations_scope": "finite signed Int.add/sub/mul expressions over constants, row/column values and affine array reads; source-used read slots only; concrete load/store with source-anchored object bases and checked finite common domain",
        "anchored_nonzero_affine_c_accesses_scope": "nonnegative constant offsets and aggregate coefficients, checked common domain, source-proved zero-address anchors covering every requested actual array object",
        "zero_origin_affine_c_accesses_proved": True,
        "zero_origin_affine_c_accesses_scope": "signed affine expressions over both loop indices, zero constant coefficient, nonnegative aggregate coefficients and independently checked finite common domain; affine copies may mix with existing recognized layout operations",
        "heterogeneous_layout_operation_list_scope": "parameterized affine inner bound, arbitrary finite list of recognized named writes/updates or independent-layout copies, compatible repeated array extents, and checked common domain",
        "candidate_interval_condition_search_verified": True,
        "candidate_condition_search_scope": "default domain and outer-count caps 8,4,3,2,1; on rejection, verified source package restricted to inner-width upper cap 1 and same independent checking repeated; affine mapped candidates, generated schedules and two-dimensional tiling",
        "source_body_range_restriction_semantics_independent": True,
        "candidate_inner_width_condition_search_verified": True,
        "parametric_affine_inner_c_bound_decoded": True,
        "affine_bound_eager_reads_and_machine_encoding_proved": True,
        "affine_parameter_guard_short_circuit_safety_proved": True,
        "affine_bound_endpoint_condition_synthesis_proved": True,
        "affine_inner_bound_tiling_csem_asm_proved": True,
        "parametric_c_source_scope": "signed affine inner upper bounds, zero initial counters, named fixed-layout arrays and existing mixed statements; first row nonempty and all rows within layout required for fast path",
        "pointer_buffer_c_source_decoded_and_guarded": True,
        "pointer_buffer_c_source_scope": "one stable signed-int pointer with arbitrary block and base offset, canonical rectangular counted loops of finite depth, finite affine reads and Int.add/sub/mul assignments; independent full-source checks, mapped candidates, schedules and outer-two-axis tiling; window is logical and is not an allocation-size assumption",
        "pointer_buffer_physical_nonalias_closed": True,
        "pointer_buffer_logical_window": 1024,
        "pointer_buffer_condition_search_caps": [2147483647, 8, 4, 3, 2, 1],
        "pointer_buffer_guard_reads_pointer": False,
        "pointer_buffer_stable_parameter_frame_proved": True,
        "pointer_buffer_multiple_distinct_pointer_variables_supported": True,
        "multi_pointer_source_and_candidate_clight_bridge_proved": True,
        "multi_pointer_guard_synthesized_from_activated_source_footprint": True,
        "multi_pointer_guard_only_evaluates_active_source_addresses": True,
        "multi_pointer_compact_sequential_guard_lowering_proved": True,
        "candidate_request_has_explicit_source_coordinates_and_context_arity": True,
        "multi_pointer_guard_continuations_not_distributed_through_tree": True,
        "multi_pointer_dynamic_separation_implies_restricted_nonalias": True,
        "multi_pointer_source_capabilities_derived_from_real_loads_and_stores": True,
        "multi_pointer_no_allocation_extent_assumption": True,
        "multi_pointer_source_allows_aliasing_before_guard": True,
        "multi_pointer_candidate_unrestricted_back_to_actual_memory": True,
        "multi_pointer_csem_asm_route_proved": True,
        "multi_pointer_potential_access_entries_resource_limit": 64,
        "multi_pointer_resource_limit_applies_to_finite_guard_path_only": True,
        "private_stateful_check_to_projected_region_contract_proved": True,
        "loop_based_alias_guard_clight_execution_proved": True,
        "loop_based_alias_guard_scope": "one canonical counted axis, exactly two accessed pointer identifiers, unit-stride zero-offset accesses, arbitrary finite read/write operation lists and stable RHS scalars; actual source-derived valid aligned addresses; quadratic runtime checks, three private temporaries, cap up to logical window 1024; mapped and generated-schedule candidates",
        "loop_based_alias_guard_code_size_independent_of_runtime_count": True,
        "loop_based_alias_guard_does_not_read_source_data": True,
        "loop_based_alias_guard_csem_asm_route_proved": True,
        "multi_pointer_condition_search_caps": [8,4,3,2,1],
        "multi_pointer_guard_scope": "pairwise separation of distinct logical access cells in the activated rectangular source footprint; conservative for read-read aliasing; distinct blocks and same-block slices supported",
        "multi_pointer_source_scope": "finite canonical rectangular counted loops, multiple stable signed-int pointer temporaries, arbitrary base offsets, signed affine coordinate addresses, stable RHS scalars, actual machine integer read/compute/write statements, mapped candidates, schedules, and outer-two-axis tiling",
        "fixed_array_external_rhs_scalars_supported": True,
        "fixed_array_scalar_scope": "actual local and global fixed-layout array objects, any finite stable signed-int RHS temporaries, recursive rectangular counted sources, mapped candidates, schedules and outer-two-axis tiling; actual descriptor coverage and physical block separation checked",
        "scalar_access_zero_column_padding_semantics_proved": True,
        "signed_affine_source_access_box_check_proved": True,
        "signed_affine_access_check_preserves_nonnegative_acceptance": True,
        "signed_affine_access_scope": "positive and negative coordinate coefficients, independently checked final mathematical cell bounds; actual machine expression evaluated modularly with the existing source theorem",
        "pointer_buffer_external_rhs_scalars_supported": True,
        "pointer_buffer_scalar_scope": "stable signed-int RHS temporaries used by actual source assignments; full signed range, any finite number; scalar arguments carried through candidates and tiling and independently validated",
        "pointer_buffer_scalar_guard_reads_scalar": False,
        "pointer_buffer_scalar_source_typing_derived_from_first_used_assignment": True,
        "point_coordinate_arity_generalized": True,
        "recursive_c_source_decoded_and_guarded": True,
        "recursive_c_source_scope": "arbitrary finite depth canonical signed counted loops with reset child iterators and stable bound temporaries; complete original body ASTs independently checked, finite common positive source-anchored array box, finite affine-read machine integer computations, short-circuit guard safe from source execution; mapped candidates, schedules and outer-two-axis tiling with all inner loops retained; finite fresh private pool may reject candidates",
        "triple_c_source_decoded_and_guarded": True,
        "triple_c_source_scope": "three nested signed canonical for loops with reset child counters, stable bound temporaries, finite common positive box derived from fixed arrays, finite affine-read Int.add/sub/mul assignment lists, source-anchored bases; mapped candidates, schedules and outer-two-axis tiling independently checked; exact public counter exits",
        "sources": {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
                    for path in sources},
        "upstream_profile": "build/polcert-optimizer-report.json",
        "upstream_proof_dependencies_rebuilt_in_this_audit": False,
    }
    (ROOT / "build" / "guard-memory-proof-report.json").write_text(json.dumps(result, indent=2) + "\n")
    print(f"Concrete Mem INSTR compiled: physical nonalias closed, {len(names(instruction))} inherited "
          f"instruction, {len(names(adapted))} unchanged validator and {len(names(compiler))} "
          "CompCert/validator union compiler assumptions")


if __name__ == "__main__":
    main()

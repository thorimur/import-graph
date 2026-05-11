/-
Copyright (c) 2024 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Eugster
-/
module

public import Lean.Data.NameMap.Basic
public import Lean.Environment
import Lean.Meta.Match.MatcherInfo
import ImportGraph.Graph.Layers
import ImportGraph.Graph.LayeredLayout

open Lean

namespace ImportGraph

open Elab Meta in
/-- Filter Lean internal declarations -/
private def isBlackListed (env : Environment) (declName : Name) : Bool :=
  declName == ``sorryAx
  || declName matches .str _ "inj"
  || declName matches .str _ "noConfusionType"
  || declName.isInternalDetail
  || isAuxRecursor env declName
  || isNoConfusion env declName
  || isRecCore env declName
  || isMatcherCore env declName

/-- Get number of non-blacklisted declarations per file. -/
public def getNumberOfDeclsPerFile (env: Environment) : NameMap Nat :=
  env.const2ModIdx.fold (fun acc n (idx : ModuleIdx) =>
    let mod := env.allImportedModuleNames[idx]!
    if isBlackListed env n then acc else acc.insert mod ((acc.getD mod 0) + 1)
    ) {}

/-- Gexf template for a node in th graph. -/
private def Gexf.nodeTemplate (n module : Name) (size layer layerX : Nat) := s!"<node id=\"{n}\" label=\"{n}\"><attvalues><attvalue for=\"0\" value=\"{size}\" /><attvalue for=\"1\" value=\"{module.isPrefixOf n}\" /><attvalue for=\"2\" value=\"{layer}\" /><attvalue for=\"3\" value=\"{layerX}\" /></attvalues></node>\n          "

/-- Gexf template for an edge in the graph -/
private def Gexf.edgeTemplate (source target : Name) := s!"<edge source=\"{source}\" target=\"{target}\" id=\"{source}--{target}\" />\n          "

open Gexf in
/-- Creates a `.gexf` file of the graph, see https://gexf.net/

Metadata can be stored in forms of attributes, currently we record the following:
* `decl_count` (Nat): number of declarations in the file
* `in_module` (Bool): whether the file belongs to the main module
  (used to strip the first part of the name when displaying).
* `layer` (Nat): topological layer (longest dependency chain ending at this
  node), used by layered layouts in the visualization.
* `layerX` (Nat): within-layer index from a barycenter sweep over the
  layered DAG, used by layered layouts in the visualization.
-/
public def Graph.toGexf (graph : NameMap (Array Name)) (module : Name) (sizes : NameMap Nat) : String :=
  let layers : NameMap Nat := graph.topologicalLayers
  let layerXs : NameMap Nat := graph.withinLayerIndices layers
  let nodes : String := graph.foldl
    (fun acc n _ => acc ++ nodeTemplate n module
      (sizes.getD n 0) (layers.getD n 0) (layerXs.getD n 0)) ""
  let edges : String := graph.foldl (fun acc n i => acc ++ (i.foldl (fun b j => b ++ edgeTemplate j n) "")) ""
  s!"<?xml version='1.0' encoding='utf-8'?>
    <gexf xmlns=\"http://www.gexf.net/1.2draft\" xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\" xsi:schemaLocation=\"http://www.gexf.net/1.2draft http://www.gexf.net/1.2draft/gexf.xsd\" version=\"1.2\">
      <meta>
        <creator>Lean ImportGraph</creator>
      </meta>
      <graph defaultedgetype=\"directed\" mode=\"static\" name=\"\">
        <attributes mode=\"static\" class=\"node\">
          <attribute id=\"0\" title=\"decl_count\" type=\"long\" />
          <attribute id=\"1\" title=\"in_module\" type=\"boolean\" />
          <attribute id=\"2\" title=\"layer\" type=\"long\" />
          <attribute id=\"3\" title=\"layerX\" type=\"long\" />
        </attributes>
        <nodes>
          {nodes.trimAscii}
        </nodes>
        <edges>
          {edges.trimAscii}
        </edges>
      </graph>
    </gexf>
    "

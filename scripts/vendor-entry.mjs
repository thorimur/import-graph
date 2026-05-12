// Entry point bundled by `scripts/build-vendor.mjs` into a single IIFE that
// exposes globals matching the legacy shape used by `html-template/index.html`.
//
// Re-exposed globals:
//   - `Sigma.Sigma`           : the Sigma constructor (matching v2's UMD shape)
//   - `graphology.Graph`      : the Graph constructor
//   - `graphologyLibrary`     : { gexf, operators, traversal, layoutForceAtlas2, FA2Layout }
//   - `SigmaNodeBorder.createNodeBorderProgram` : factory for bordered nodes

import Sigma from "sigma";
import Graph from "graphology";
import * as gexf from "graphology-gexf/browser";
import * as operators from "graphology-operators";
import * as traversal from "graphology-traversal";
import * as forceatlas2 from "graphology-layout-forceatlas2";
import FA2Layout from "graphology-layout-forceatlas2/worker";
import { createNodeBorderProgram } from "@sigma/node-border";

window.Sigma = { Sigma };
window.graphology = { Graph };
window.graphologyLibrary = {
  gexf,
  operators,
  traversal,
  layoutForceAtlas2: forceatlas2,
  FA2Layout,
};
window.SigmaNodeBorder = { createNodeBorderProgram };

# Vendor bundle

`sigma-bundle.min.js` is built from these packages (all MIT-licensed); see
each upstream repository for full license text.

| Package                          | Repository                                              |
| -------------------------------- | ------------------------------------------------------- |
| sigma                            | https://github.com/jacomyal/sigma.js                    |
| graphology                       | https://github.com/graphology/graphology                |
| graphology-gexf                  | https://github.com/graphology/graphology                |
| graphology-operators             | https://github.com/graphology/graphology                |
| graphology-traversal             | https://github.com/graphology/graphology                |
| graphology-layout-forceatlas2    | https://github.com/graphology/graphology                |
| @sigma/node-border               | https://github.com/jacomyal/sigma.js                    |

Built from `scripts/vendor-entry.mjs` via `node scripts/build-vendor.mjs`.
Regenerate the bundle after bumping versions in `package.json`.

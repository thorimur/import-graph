module

/- This root module deliberately does *not* import the fixture files under `FindHomeB/`
that contain `#find_home` invocations — those are only ever elaborated by the language
server, via the harness in `ImportGraphTest/FindHome/Harness.lean`. It imports everything
those fixture files import, so that `lake build` in this package pre-builds all of their
dependencies and serving them is fast and deterministic. -/

public import ImportGraph.Tools.FindHome
public import FindHomeA
public import FindHomeB.Local1

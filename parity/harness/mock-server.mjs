// A scripted HTTP server for the parity harness. No dependencies.
//
// The script maps a path to a list of responses. The nth request to a path gets the nth
// response; once the list runs out, the last one repeats. An unknown path is a 404.
//
//   { "/v1/api": [{ "status": 503 }, { "status": 200, "body": { "status": "ok" } }] }
//
// A response is { status, body?, text?, contentType?, delayMs? }, or { drop: true }.
// - `body` is sent as JSON with content type application/json.
// - `text` is sent as-is with `contentType` (default text/plain).
// - `drop` counts the request, then destroys the socket without answering: a network error.
// Every response sends `Connection: close`, so no client can reuse a socket the server is closing.
import { createServer } from "node:http"

const send = (res, r) => {
  const write = () => {
    if (r.drop) {
      res.socket?.destroy()
    } else if (r.status === 304 || r.status === 204) {
      res.writeHead(r.status, { connection: "close" })
      res.end()
    } else if (r.text !== undefined) {
      res.writeHead(r.status, { "content-type": r.contentType ?? "text/plain", connection: "close" })
      res.end(r.text)
    } else {
      res.writeHead(r.status, { "content-type": r.contentType ?? "application/json", connection: "close" })
      res.end(JSON.stringify(r.body ?? {}))
    }
  }
  // unref: a response the client gave up on must not keep the harness running.
  if (r.delayMs) setTimeout(write, r.delayMs).unref()
  else write()
}

/** Starts a fresh server on a free port. `requests` counts requests per path. */
export const startMock = (script) =>
  new Promise((resolve) => {
    const requests = {}
    const server = createServer((req, res) => {
      const path = new URL(req.url, "http://localhost").pathname
      const n = requests[path] ?? 0
      requests[path] = n + 1
      const responses = script[path]
      if (!responses || responses.length === 0) return send(res, { status: 404, body: { error: "no such path" } })
      send(res, responses[Math.min(n, responses.length - 1)])
    })
    server.listen(0, "127.0.0.1", () => {
      const { port } = server.address()
      resolve({
        url: `http://127.0.0.1:${port}`,
        requests,
        close: () =>
          new Promise((done) => {
            server.closeAllConnections()
            server.close(() => done())
          }),
      })
    })
  })

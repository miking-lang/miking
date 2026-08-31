-- # Simple Local Doc Server
--
-- This file defines a small utility to preview the generated documentation.
-- 
-- It embeds a Python script (`pythonScript`) which:
-- - starts a local HTTP server on port 3000
-- - serves the generated outputs as HTML (using Python’s `markdown` module if output is markdown)
-- - auto-opens the browser
-- 
-- ## How it works:
-- 
-- - `startServer` writes the Python script to a temporary file
-- - launches it with:
--   ```bash
--   python3 script.py <out-dir dir> <initial object>
--   ```

include "sys.mc"
include "./server-options.mc"
include "../global/util.mc"
include "../global/ext-utils.mc"
include "seq.mc"
include "basic-types.mc"
include "ext/file-ext.mc"

let pythonScript = lam servesMd. join ["
import os
from http.server import HTTPServer, BaseHTTPRequestHandler
from urllib.parse import unquote
import mimetypes
import webbrowser
import threading
",
if servesMd then
"import markdown"
else
"", "
import sys

DOC_DIR = sys.argv[1]

class Handler(BaseHTTPRequestHandler):
    def do_GET(self):
        path = unquote(self.path.lstrip('/'))
        file_path = os.path.join(DOC_DIR, path)

        if not os.path.isfile(file_path):
            self.send_response(404)
            self.send_header('Content-type', 'text/plain; charset=utf-8')
            self.end_headers()
            self.wfile.write(f\"File not found: {file_path}\".encode('utf-8'))
            return

        # Serve markdown or html as text/html
        if ",
if servesMd then "file_path.endswith('.md') or " else "", 
"file_path.endswith('.html'):
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
",
if servesMd then
"            if file_path.endswith('.md'):
                content = markdown.markdown(content)"
else
"", "

            self.send_response(200)
            self.send_header('Content-type', 'text/html; charset=utf-8')
            self.end_headers()
            self.wfile.write(content.encode('utf-8'))
        else:
            self.serve_static_file(file_path)

    def serve_static_file(self, file_path):
        if not os.path.isfile(file_path):
            self.send_response(404)
            self.send_header('Content-type', 'text/plain; charset=utf-8')
            self.end_headers()
            self.wfile.write(f\"File not found: {file_path}\".encode('utf-8'))
            return
        
        content_type, _ = mimetypes.guess_type(file_path)
        content_type = content_type or 'application/octet-stream'

        with open(file_path, 'rb') as f:
            content = f.read()

        self.send_response(200)
        self.send_header('Content-type', content_type)
        self.end_headers()
        self.wfile.write(content)


server_address = ('127.0.0.1', 3000)
httpd = HTTPServer(server_address, Handler)
print(\"Server started on http://127.0.0.1:3000\")
def open_url():
    webbrowser.open('127.0.0.1:3000' + sys.argv[2])

t = threading.Thread(target=open_url)
t.start()

try:
    httpd.serve_forever()
except KeyboardInterrupt:
    pass
finally:
    httpd.server_close()
"]

let pythonServerStart : Bool -> ServerOptions -> () = lam servesMd. lam opt.
    let file = sysTempFileMake () in
    match docgenFileWriteOpen file with Some wc then
        let write = docgenFileWriteString wc in
        write (pythonScript servesMd);
        fileWriteFlush wc;
        fileWriteClose wc;
        let pwd = sysGetCwd () in
        let path = normalizePath (join [pwd, "/", opt.folder]) in
        let res = sysRunCommand ["python3", file, path, opt.link] "" "/" in ()
        
    else error "Failed to open temporary file. The browser failed to start but the files have been generated."

"""Static file server with HTTP Range support, so browsers can seek in videos: `serve_range.py PORT DIR [--open PATH]`."""

import functools
import http.server
import os
import subprocess
import sys
import threading


class Handler(http.server.SimpleHTTPRequestHandler):
    def send_head(self):
        self._left = None  # the handler is reused across a keep-alive connection
        rng = self.headers.get("Range")
        path = self.translate_path(self.path)
        if not rng or not rng.startswith("bytes=") or not os.path.isfile(path):
            return super().send_head()
        size = os.path.getsize(path)
        a, _, b = rng[len("bytes="):].split(",")[0].partition("-")
        try:
            start = int(a) if a else max(0, size - int(b))
            end = min(int(b) if (a and b) else size - 1, size - 1)
        except ValueError:
            return super().send_head()
        if start > end:
            self.send_error(416)
            return None
        f = open(path, "rb")
        f.seek(start)
        self.send_response(206)
        self.send_header("Content-Type", self.guess_type(path))
        self.send_header("Content-Range", f"bytes {start}-{end}/{size}")
        self.send_header("Content-Length", str(end - start + 1))
        self.end_headers()
        self._left = end - start + 1
        return f

    def copyfile(self, src, dst):
        left = self._left
        if left is None:
            return super().copyfile(src, dst)
        while left > 0:
            buf = src.read(min(65536, left))
            if not buf:
                break
            dst.write(buf)
            left -= len(buf)

    def end_headers(self):
        self.send_header("Accept-Ranges", "bytes")
        self.send_header("Cache-Control", "no-cache")
        super().end_headers()


def main() -> None:
    port, root = int(sys.argv[1]), sys.argv[2]
    page = sys.argv[sys.argv.index("--open") + 1] if "--open" in sys.argv else None
    try:
        server = http.server.ThreadingHTTPServer(("127.0.0.1", port), functools.partial(Handler, directory=root))
    except OSError as e:
        sys.exit(f"port {port} is not free ({e.strerror}); pick another, e.g. `make present PORT={port + 1}`")
    url = f"http://127.0.0.1:{port}/{page or ''}"
    print(f"serving {root} at {url} (Ctrl-C to stop)", flush=True)
    if page:
        threading.Timer(0.3, lambda: subprocess.run(["open", url], check=False)).start()
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass


if __name__ == "__main__":
    main()

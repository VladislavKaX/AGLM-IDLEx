import tkinter as tk
from tkinter import filedialog, messagebox, ttk, font
import subprocess
import threading
import tempfile
import os
import sys
import queue
import signal
import re
import shutil
import json
import tokenize, io, token
import keyword
import builtins

if getattr(sys, "frozen", False):
    # app is frozen as EXE (PyInstaller). Don't treat the EXE itself as a Python interpreter.
    CURRENT_EXE_BASENAME = os.path.basename(sys.executable).lower()
    # try to find a system python that is NOT the current exe
    import shutil

    PYTHON = None
    for candidate in ("python", "python3", "py"):
        p = shutil.which(candidate)
        if p and os.path.basename(p).lower() != CURRENT_EXE_BASENAME:
            PYTHON = p
            break
    # base path for bundled files
    BASE_PATH = getattr(sys, "_MEIPASS", os.path.dirname(__file__))
else:
    PYTHON = sys.executable
    BASE_PATH = os.path.dirname(__file__)
USER_CONFIG = os.path.join(os.path.expanduser("~"), ".idlex_config.json")
BUNDLED_CONFIG = os.path.join(
    BASE_PATH, "idle_config.json"
)  # only exists when not installed
# read: prefer USER_CONFIG, fallback to BUNDLED_CONFIG
CONFIG_FILE = USER_CONFIG if os.path.exists(USER_CONFIG) else BUNDLED_CONFIG

# ---------- Configuration ----------
# --- Regex patterns ---

KEYWORDS = r"\b(?:def|class|if|elif|else|try|except|finally|for|while|with|as|import|from|return|yield|pass|break|continue|and|or|not|in|is|lambda|global|nonlocal|assert|del|raise|True|False|None)\b"
COMMENT = r"#.*"
STRING = r"(?:'[^'\\]*(?:\\.[^'\\]*)*'|\"[^\"\\]*(?:\\.[^\"\\]*)*\")"
NUMBERS = r"\b\d+(?:\.\d+)?\b"
BUILTINS = r"\b(?:print|len|range|open|input|str|int|float|list|dict|set|tuple|map|filter|zip|enumerate|sum|min|max|any|all|abs|dir|help|type|isinstance|super)\b"
FUNCTION_DEF = r"\bdef\s+([A-Za-z_][A-Za-z0-9_]*)"
CLASS_DEF = r"\bclass\s+([A-Za-z_][A-Za-z0-9_]*)"
DECORATOR = r"@\w+"

HIGHLIGHT_DELAY = 300  # ms

LIGHT_THEME = {
    "background": "#ffffff",
    "foreground": "#000000",
    "console_bg": "#f7f7f7",
    "console_fg": "#000000",
}

DARK_THEME = {
    "background": "#1e1e1e",
    "foreground": "#d4d4d4",
    "keyword": "#569cd6",
    "comment": "#6a9955",
    "string": "#ce9178",
    "number": "#b5cea8",
    "builtin": "#dcdcaa",
    "function": "#dcdcaa",
    "class": "#4ec9b0",
    "decorator": "#c586c0",
    "console_bg": "#000000",
    "console_fg": "#ffffff",
}


class LineNumberCanvas(tk.Canvas):
    def __init__(self, master, text_widget, font_obj=None, **kwargs):
        # DO NOT pass any 'font' kw to Canvas.__init__
        super().__init__(master, **kwargs)
        self.text_widget = text_widget

        # Ensure we always have a tkinter.font.Font object
        if isinstance(font_obj, font.Font):
            self.font = font_obj
        else:
            try:
                # font_obj may be a tuple or string acceptable by Font()
                self.font = font.Font(font=font_obj)
            except Exception:
                # fallback
                self.font = font.Font(family="Consolas", size=11)

        self.line_height = int(self.font.metrics("linespace") or 1)

        # redraw when text widget changes/scrolls/resizes
        self.text_widget.bind("<Configure>", lambda e: self.redraw())
        self.text_widget.bind("<<Change>>", lambda e: self.redraw())
        self.text_widget.bind("<KeyRelease>", lambda e: self.redraw())
        # mouse wheel events on some platforms:
        self.text_widget.bind("<MouseWheel>", lambda e: self.redraw(), add="+")
        self.text_widget.bind("<ButtonRelease-1>", lambda e: self.redraw(), add="+")

    def set_font(self, font_obj):
        """Set/replace the internal Font object (font_obj can be Font or tuple)."""
        if isinstance(font_obj, font.Font):
            self.font = font_obj
        else:
            try:
                self.font = font.Font(font=font_obj)
            except Exception:
                self.font = font.Font(family="Consolas", size=11)
        self.line_height = int(self.font.metrics("linespace") or 1)
        self.redraw()

    def redraw(self):
        # draw only visible lines, aligned to text widget dlineinfo for the first visible
        self.delete("all")
        try:
            first_index = self.text_widget.index("@0,0")
        except Exception:
            return
        dline = self.text_widget.dlineinfo(first_index)
        y = dline[1] if dline else 0
        first_line = int(first_index.split(".")[0])

        # compute how many lines fit vertically (safe fallback)
        height_px = self.text_widget.winfo_height() or (self.line_height * 30)
        visible = int(height_px / max(1, self.line_height)) + 2
        last_line = first_line + visible

        # Draw lines using the Font object (Tkinter accepts Font objects here)
        for i in range(first_line, last_line):
            self.create_text(
                2, y, anchor="nw", text=str(i), font=self.font, fill="#616161"
            )
            y += self.line_height

    def yview(self, *args):
        # used when scrolling from scrollbar; delegate to text widget then redraw
        try:
            self.text_widget.yview(*args)
        finally:
            self.redraw()


class SimplePythonIDE(tk.Tk):
    def __init__(self):
        super().__init__()
        self.highlight_after_id = None

        self.title("IDLEx - fastest Python interpreter")
        self.geometry("1000x850")

        # Be robust if icon file doesn't exist or platform doesn't support .ico
        try:
            icon_path = os.path.join(BASE_PATH, "icon.ico")
            if os.path.exists(icon_path):
                # .iconbitmap works for .ico on Windows
                self.iconbitmap(icon_path)
        except Exception:
            pass

        # Per-tab file tracking is stored in self.tabs mapping
        self.tempfile_path = None  # Track temporary files
        self.process = None
        self.proc_lock = threading.Lock()
        self.output_queue = queue.Queue()
        self.theme = LIGHT_THEME  # Initialize theme
        self.python_keywords = set(keyword.kwlist)
        self.python_builtins = set(dir(builtins))
        self.options = {
            "show_line_numbers": True,
            "word_wrap": False,
        }

        self.python_interpreter = PYTHON  # Start with auto-detected one

        self._load_config()
        self._build_ui()
        self._restore_session()
        self._apply_theme()
        self._bind_shortcuts()
        self._highlight_heartbeat()
        self.protocol("WM_DELETE_WINDOW", self._on_close)

        # -------------------------- UI --------------------------

    def _build_ui(self):
        self._create_menu()
        self._create_toolbar()

        # -------- Main horizontal split: Explorer | Editor --------
        main_pane = ttk.Panedwindow(self, orient=tk.HORIZONTAL)
        main_pane.pack(fill=tk.BOTH, expand=True)

        # Explorer (left)
        explorer_frame = tk.Frame(main_pane, width=240, bg="#f0f0f0")
        explorer_label = tk.Label(explorer_frame, text="Project Explorer", anchor="w")
        explorer_label.pack(fill=tk.X)

        self.file_tree = ttk.Treeview(
            explorer_frame, columns=("fullpath",), show="tree"
        )
        self.file_tree.heading("#0", text="Name", anchor="w")
        self.file_tree.column("fullpath", width=0, stretch=False)
        self.file_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        vsb = ttk.Scrollbar(
            explorer_frame, orient="vertical", command=self.file_tree.yview
        )
        self.file_tree.configure(yscrollcommand=vsb.set)
        vsb.pack(side=tk.RIGHT, fill=tk.Y)

        self.file_tree.bind("<Double-1>", self._on_tree_double_click)
        main_pane.add(explorer_frame, weight=1)

        # Editor (right)
        editor_frame = ttk.Frame(main_pane)
        self.notebook = ttk.Notebook(editor_frame)
        self.notebook.pack(fill=tk.BOTH, expand=True)
        self.tabs = {}

        self._init_tab_context_menu()
        self.notebook.bind("<Button-3>", self._show_tab_menu)
        # No line numbers widget here: each tab creates its own
        self._new_tab("Untitled")

        main_pane.add(editor_frame, weight=4)

        # -------- Console + Input (bottom split) --------
        console_pane = ttk.Panedwindow(self, orient=tk.HORIZONTAL)
        console_pane.pack(fill=tk.BOTH, side=tk.BOTTOM, expand=False)

        # Console
        console_side = tk.Frame(console_pane)
        console_label = tk.Label(console_side, text="Console", anchor="w")
        console_label.pack(fill=tk.X)

        self.console = tk.Text(console_side, height=9, state="disabled", width=70)
        self.console.pack(fill=tk.BOTH, expand=True)
        console_pane.add(console_side, weight=3)

        # Input
        input_side = tk.Frame(console_pane)
        input_label = tk.Label(input_side, text="Input", anchor="w")
        input_label.pack(fill=tk.X)

        self.console_input = tk.Text(input_side, height=9, width=34)
        self.console_input.pack(fill=tk.BOTH, expand=True)
        self.console_input.bind("<Return>", self._send_input)
        console_pane.add(input_side, weight=1)

        # -------- Status bar --------
        self.status = tk.Label(self, text="Ready", anchor="w")
        self.status.pack(fill=tk.X, side=tk.BOTTOM)

        # Reapply theme & schedule highlight on tab change
        self.notebook.bind(
            "<<NotebookTabChanged>>",
            lambda e: (self._apply_theme(), self.schedule_highlight()),
        )
        self.highlight_after_id = None

    def _create_toolbar(self):
        toolbar = tk.Frame(self, bd=1, relief=tk.RAISED)
        tk.Button(toolbar, text="Open", command=self.open_file).pack(
            side=tk.LEFT, padx=2, pady=2
        )
        tk.Button(toolbar, text="Save", command=self.save_file).pack(
            side=tk.LEFT, padx=2, pady=2
        )
        tk.Button(toolbar, text="Save As", command=self.save_file_as).pack(
            side=tk.LEFT, padx=2, pady=2
        )
        tk.Button(toolbar, text="Run", command=self.run_code).pack(
            side=tk.LEFT, padx=2, pady=2
        )
        tk.Button(toolbar, text="Stop", command=self.stop_code).pack(
            side=tk.LEFT, padx=2, pady=2
        )
        tk.Button(
            toolbar, text="New Tab", command=lambda: self._new_tab("Untitled")
        ).pack(side=tk.LEFT, padx=2, pady=2)
        tk.Button(toolbar, text="Load Folder", command=self._load_folder).pack(
            side=tk.LEFT, padx=2, pady=2
        )
        toolbar.pack(side=tk.TOP, fill=tk.X)

    def _create_menu(self):
        menubar = tk.Menu(self)

        filemenu = tk.Menu(menubar, tearoff=0)
        filemenu.add_command(label="Open", command=self.open_file, accelerator="Ctrl+O")
        filemenu.add_command(label="Save", command=self.save_file, accelerator="Ctrl+S")
        filemenu.add_command(
            label="Save As", command=self.save_file_as, accelerator="Ctrl+Shift+S"
        )
        filemenu.add_command(
            label="New Tab",
            command=lambda: self._new_tab("Untitled"),
            accelerator="Ctrl+N",
        )
        filemenu.add_command(label="Load Folder", command=self._load_folder)
        filemenu.add_separator()
        filemenu.add_command(label="Exit", command=self._on_close)
        menubar.add_cascade(label="File", menu=filemenu)

        runmenu = tk.Menu(menubar, tearoff=0)
        runmenu.add_command(label="Run", command=self.run_code, accelerator="F5")
        runmenu.add_command(
            label="Stop", command=self.stop_code, accelerator="Shift+F5"
        )
        menubar.add_cascade(label="Run", menu=runmenu)

        viewmenu = tk.Menu(menubar, tearoff=0)
        viewmenu.add_command(label="Toggle Theme", command=self.toggle_theme)
        viewmenu.add_command(
            label="Zoom In", command=lambda: self.zoom(1), accelerator="Ctrl+= / Ctrl++"
        )
        viewmenu.add_command(
            label="Zoom Out", command=lambda: self.zoom(-1), accelerator="Ctrl+-"
        )
        menubar.add_cascade(label="View", menu=viewmenu)

        # Interpreter menu
        self.interpmenu = tk.Menu(menubar, tearoff=0)
        self._populate_interpreter_menu()
        menubar.add_cascade(label="Interpreter", menu=self.interpmenu)

        # Options menu
        options_menu = tk.Menu(menubar, tearoff=0)

        # Toggle: Show Line Numbers
        self.show_line_numbers_var = tk.BooleanVar(value=True)
        options_menu.add_checkbutton(
            label="Show Line Numbers",
            onvalue=True,
            offvalue=False,
            variable=self.show_line_numbers_var,
            command=self._toggle_line_numbers,
        )

        # Toggle: Word Wrap
        self.word_wrap_var = tk.BooleanVar(value=False)
        options_menu.add_checkbutton(
            label="Word Wrap",
            onvalue=True,
            offvalue=False,
            variable=self.word_wrap_var,
            command=self._toggle_word_wrap,
        )
        options_menu.add_command(
            label="Advanced Settings...", command=self._show_advanced_settings
        )

        menubar.add_cascade(label="Options", menu=options_menu)

        self.config(menu=menubar)

    def _populate_interpreter_menu(self):
        self.interpmenu.delete(0, tk.END)
        interpreters = self._find_python_interpreters()

        # Create the shared variable if it does not exist yet
        if not hasattr(self, "selected_interpreter_var"):
            self.selected_interpreter_var = tk.StringVar(
                value=getattr(self, "python_interpreter", sys.executable)
            )

        for version, path in interpreters:
            label = f"{version}  —  {path}"
            self.interpmenu.add_radiobutton(
                label=label,
                value=path,
                variable=self.selected_interpreter_var,
                command=lambda p=path: self._set_interpreter(p),
            )

        self.interpmenu.add_separator()
        self.interpmenu.add_command(
            label="Set Custom Interpreter...", command=self._set_python_interpreter
        )

    def _find_python_interpreters(self):
        import shutil
        import subprocess

        paths = []
        candidates = [
            "python",
            "python3",
            "python3.12",
            "python3.11",
            "python3.10",
            "python3.9",
            "py",
        ]

        # Search in PATH
        for name in candidates:
            p = shutil.which(name)
            if p and p not in paths:
                # If frozen, skip if p is this exe
                if (
                    getattr(sys, "frozen", False)
                    and os.path.basename(p).lower()
                    == os.path.basename(sys.executable).lower()
                ):
                    continue
                paths.append(p)

        if sys.platform == "win32":
            # Scan common install locations (keeps same behavior but avoid duplicates)
            local_python_dir = os.path.expanduser(r"~\AppData\Local\Programs\Python")
            if os.path.isdir(local_python_dir):
                for root, dirs, files in os.walk(local_python_dir):
                    if "python.exe" in files:
                        exe = os.path.join(root, "python.exe")
                        if exe not in paths and not (
                            getattr(sys, "frozen", False)
                            and os.path.basename(exe).lower()
                            == os.path.basename(sys.executable).lower()
                        ):
                            paths.append(exe)

        # Add custom interpreters stored in config_data safely
        custom_list = []
        if hasattr(self, "config_data") and isinstance(self.config_data, dict):
            custom_list = self.config_data.get("custom_interpreters", [])

        for exe in custom_list:
            if (
                os.path.isfile(exe)
                and exe not in paths
                and not (
                    getattr(sys, "frozen", False)
                    and os.path.basename(exe).lower()
                    == os.path.basename(sys.executable).lower()
                )
            ):
                paths.append(exe)

        # Get version info for display (hide transient consoles on Windows)
        result = []
        for exe in paths:
            try:
                kwargs = dict(stderr=subprocess.STDOUT, text=True, timeout=2)
                if sys.platform == "win32":
                    kwargs["creationflags"] = subprocess.CREATE_NO_WINDOW
                version_output = subprocess.check_output(
                    [exe, "--version"], **kwargs
                ).strip()
            except Exception:
                version_output = "Unknown version"
            result.append((version_output, exe))

        return result

    def _load_folder_from_path(self, folder):
        """Load a folder into the file tree without showing a dialog."""
        if not folder or not os.path.isdir(folder):
            return

        self.project_folder = folder
        for child in self.file_tree.get_children():
            self.file_tree.delete(child)

        def insert_node(parent, path):
            name = os.path.basename(path) if parent else path
            node_id = self.file_tree.insert(parent, "end", text=name, open=False)
            self.file_tree.set(node_id, "fullpath", path)
            if os.path.isdir(path):
                try:
                    entries = sorted(os.listdir(path), key=lambda s: s.lower())
                except Exception:
                    entries = []
                for entry in entries:
                    full = os.path.join(path, entry)
                    if os.path.isdir(full) or full.endswith(".py"):
                        insert_node(node_id, full)

        insert_node("", folder)
        roots = self.file_tree.get_children()
        if roots:
            self.file_tree.item(roots[0], open=True)

    def _restore_session(self):
        """
        Restore interpreter, project folder and tabs from self.config_data.
        Call this after UI widgets are created (after self._build_ui()).
        """
        cfg = getattr(self, "config_data", {}) or {}

        # ---- Interpreter ----
        try:
            interp = cfg.get("python_interpreter")
            if interp and os.path.isfile(interp):
                self.python_interpreter = interp
                if not hasattr(self, "selected_interpreter_var"):
                    self.selected_interpreter_var = tk.StringVar(value=interp)
                else:
                    self.selected_interpreter_var.set(interp)
                try:
                    self._populate_interpreter_menu()
                except Exception:
                    pass
        except Exception as e:
            try:
                self._append_console(f"[Interpreter restore error: {e}]\n")
            except Exception:
                pass

        # ---- Project folder (file tree) ----
        try:
            pf = cfg.get("project_folder")
            if pf and os.path.isdir(pf):
                if hasattr(self, "_load_folder_from_path"):
                    try:
                        self._load_folder_from_path(pf)
                    except Exception as e:
                        self._append_console(f"[Project folder restore error: {e}]\n")
                else:
                    self.project_folder = pf
                    try:
                        self._load_folder_from_path(self, pf)
                    except Exception:
                        pass
        except Exception as e:
            try:
                self._append_console(f"[Folder restore error: {e}]\n")
            except Exception:
                pass

        # ---- Tabs ----
        try:
            saved_tabs = cfg.get("tabs") or []
            if isinstance(saved_tabs, list) and saved_tabs:
                # Clear any initial default tabs
                for frame in list(self.tabs.keys()):
                    try:
                        self.notebook.forget(frame)
                    except Exception:
                        pass
                    self.tabs.pop(frame, None)

                # Recreate saved tabs
                for tabobj in saved_tabs:
                    filepath = tabobj.get("filepath")
                    title = tabobj.get("title") or "Untitled"
                    content = tabobj.get("content", "") or ""
                    if filepath:
                        if os.path.isfile(filepath):
                            try:
                                with open(filepath, "r", encoding="utf-8") as f:
                                    content = f.read()
                            except Exception as e:
                                self._append_console(
                                    f"[Could not read {filepath}: {e}]\n"
                                )
                        else:
                            filepath = None  # treat as unsaved tab
                    try:
                        self._new_tab(title, filepath=filepath, content=content)
                    except Exception as e:
                        self._append_console(f"[Failed to restore tab {title}: {e}]\n")

                # Select previously active tab index
                try:
                    idx = int(cfg.get("selected_tab_index", 0))
                    tabs = self.notebook.tabs()
                    if tabs:
                        idx = max(0, min(idx, len(tabs) - 1))
                        self.notebook.select(idx)
                except Exception:
                    pass

        except Exception as e:
            try:
                self._append_console(f"[Tabs restore error: {e}]\n")
            except Exception:
                pass

        # ---- Ensure at least one tab exists ----
        if not self.tabs:
            try:
                self._new_tab("Untitled")
            except Exception:
                pass

    def _add_change_proxy(self, text_widget):
        """Monkey-patch the widget to generate <<Change>> on modifications."""
        text_widget._orig = text_widget._w + "_orig"
        text_widget.tk.call("rename", text_widget._w, text_widget._orig)
        text_widget.tk.createcommand(
            text_widget._w, lambda *args: self._proxy(text_widget, *args)
        )

    def _proxy(self, text_widget, *args):
        cmd = (text_widget._orig,) + args
        result = text_widget.tk.call(cmd)

        if (
            args[0] in ("insert", "delete", "replace")
            or args[0:3] == ("mark", "set", "insert")
            or args[0:2] == ("xview", "moveto")
            or args[0:2] == ("xview", "scroll")
            or args[0:2] == ("yview", "moveto")
            or args[0:2] == ("yview", "scroll")
        ):
            text_widget.event_generate("<<Change>>", when="tail")

        return result

    def _save_config(self):
        def _atomic_write(path, data):
            tmp = path + ".tmp"
            with open(tmp, "w", encoding="utf-8") as f:
                json.dump(data, f, indent=2)
                f.flush()
                try:
                    os.fsync(f.fileno())  # ensure data hits disk
                except Exception:
                    pass
            os.replace(tmp, path)  # atomic on most OSes

        cfg = {}
        cfg["python_interpreter"] = getattr(self, "python_interpreter", None)
        cfg["project_folder"] = getattr(self, "project_folder", None)
        # collect tabs
        tabs = []
        for frame, data in self.tabs.items():
            fp = data.get("filepath")
            if fp:
                tabs.append({"filepath": fp, "title": os.path.basename(fp)})
            else:
                # unsaved tab -> store content (limit size)
                content = data["text"].get("1.0", "end-1c")
                if len(content) > 100_000:
                    content = content[:100_000]  # avoid massive configs
                tabs.append(
                    {
                        "filepath": None,
                        "title": self.notebook.tab(frame, "text"),
                        "content": content,
                    }
                )
        cfg["tabs"] = tabs
        try:
            sel = self.notebook.index(self.notebook.select())
        except Exception:
            sel = 0
        cfg["selected_tab_index"] = sel

        # write file atomically
        try:
            _atomic_write(CONFIG_FILE, cfg)
            self.config_data = cfg  # keep in-memory snapshot
        except Exception as e:
            # non-fatal: log to console
            self._append_console(f"[Config save error: {e}]\n")

    def _load_config(self):
        cfg = {}
        try:
            if os.path.isfile(USER_CONFIG):
                with open(USER_CONFIG, "r", encoding="utf-8") as f:
                    cfg = json.load(f)
            elif os.path.isfile(BUNDLED_CONFIG):
                with open(BUNDLED_CONFIG, "r", encoding="utf-8") as f:
                    cfg = json.load(f)
        except Exception as e:
            print(f"Config load error: {e}")
            cfg = {}
        if not isinstance(cfg, dict):
            cfg = {}
        self.config_data = cfg

    def _bind_shortcuts(self):
        # File
        self.bind_all("<Control-o>", lambda e: self.open_file())
        self.bind_all("<Control-s>", lambda e: self.save_file())
        self.bind_all("<Control-S>", lambda e: self.save_file_as())
        self.bind_all("<Control-n>", lambda e: self._new_tab("Untitled"))
        # Run
        self.bind_all("<F5>", lambda e: self.run_code())
        self.bind_all("<Shift-F5>", lambda e: self.stop_code())
        # Zoom
        self.bind_all("<Control-=>", lambda e: self.zoom(1))
        self.bind_all("<Control-plus>", lambda e: self.zoom(1))
        self.bind_all("<Control-minus>", lambda e: self.zoom(-1))

    # ----------------------- File handling -----------------------
    def open_file(self):
        path = filedialog.askopenfilename(filetypes=[("Python files", "*.py")])
        if path:
            try:
                with open(path, "r", encoding="utf-8") as f:
                    code = f.read()
            except Exception as e:
                messagebox.showerror("Open File Error", str(e))
                return
            title = os.path.basename(path)

            # Reuse existing tab if already open
            for frame, data in self.tabs.items():
                if data.get("filepath") == path:
                    self.notebook.select(frame)
                    data["text"].delete("1.0", tk.END)
                    data["text"].insert("1.0", code)
                    self.schedule_highlight()
                    self.status["text"] = f"Re-opened: {path}"
                    return

            self._new_tab(title, filepath=path, content=code)
            self.status["text"] = f"Opened: {path}"

    def save_file_as(self):
        text_widget, tab_data = self._get_current_editor()
        if not text_widget:
            return False
        path = filedialog.asksaveasfilename(
            defaultextension=".py", filetypes=[("Python files", "*.py")]
        )
        if path:
            tab_data["filepath"] = path
            current_tab = self.notebook.select()
            filename = os.path.basename(path)
            self.notebook.tab(current_tab, text=filename)
            return self.save_file()
        return False

    def save_file(self):
        text_widget, tab_data = self._get_current_editor()
        if not text_widget:
            return False
        filepath = tab_data.get("filepath")
        if not filepath:
            return self.save_file_as()
        try:
            with open(filepath, "w", encoding="utf-8") as f:
                f.write(text_widget.get("1.0", tk.END))
            self.status["text"] = f"Saved: {filepath}"
            return True
        except Exception as e:
            messagebox.showerror("Save Error", str(e))
            return False

    def _set_interpreter(self, path):
        """
        Set the Python interpreter to `path`.

        - Rejects non-files.
        - When frozen, rejects the packaged EXE itself (prevents launching the app as the interpreter).
        - Ensures self.config_data exists and saves the selection.
        - Updates the radio-button var so menu shows the selected interpreter.
        """
        if not path or not os.path.isfile(path):
            self._append_console("[Interpreter not found]\n")
            return

        # Prevent selecting the packaged EXE as an interpreter when running frozen
        if getattr(sys, "frozen", False):
            try:
                exe_name = os.path.basename(sys.executable).lower()
                candidate = os.path.basename(path).lower()
                if candidate == exe_name:
                    self._append_console(
                        "[Cannot use the packaged EXE as an interpreter]\n"
                    )
                    return
            except Exception:
                # if anything goes wrong with the comparison, be conservative and reject
                self._append_console(
                    "[Interpreter selection check failed — selection rejected]\n"
                )
                return

        # Ensure we have a config_data dict to store custom interpreters
        if not hasattr(self, "config_data") or not isinstance(self.config_data, dict):
            self.config_data = {}

        # Set interpreter and update UI state
        self.python_interpreter = path

        # Ensure the shared StringVar exists and update it (so the menu shows the selected radio)
        if not hasattr(self, "selected_interpreter_var"):
            self.selected_interpreter_var = tk.StringVar(value=path)
        else:
            self.selected_interpreter_var.set(path)

        self.status.config(text=f"Python interpreter set: {path}")
        self._append_console(f"[Interpreter changed to: {path}]\n")

        # Save to custom_interpreters so it appears in the menu next time
        lst = self.config_data.setdefault("custom_interpreters", [])
        if path not in lst:
            lst.append(path)

        # Persist config and refresh menu so the checkmark updates
        try:
            self._save_config()
        except Exception as e:
            self._append_console(f"[Config save error: {e}]\n")

        # Rebuild the interpreter menu so the radio selection is correct
        try:
            self._populate_interpreter_menu()
        except Exception:
            pass

    def _set_python_interpreter(self):
        path = filedialog.askopenfilename(
            title="Select Python Interpreter",
            filetypes=[
                (
                    "Python Executable",
                    "python.exe" if sys.platform == "win32" else "python*",
                )
            ],
        )
        if path:
            if os.path.isfile(path):
                # Add to saved custom interpreters
                self.config_data.setdefault("custom_interpreters", [])
                if path not in self.config_data["custom_interpreters"]:
                    self.config_data["custom_interpreters"].append(path)
                self._save_config()  # save to idle_config.json

                self._set_interpreter(path)

    def _load_folder(self):
        folder = filedialog.askdirectory()
        if folder:
            self.project_folder = folder
            for child in self.file_tree.get_children():
                self.file_tree.delete(child)

            def insert_node(parent, path):
                name = os.path.basename(path) if parent else path
                node_id = self.file_tree.insert(parent, "end", text=name, open=False)
                self.file_tree.set(node_id, "fullpath", path)
                if os.path.isdir(path):
                    try:
                        entries = sorted(os.listdir(path), key=lambda s: s.lower())
                    except Exception:
                        entries = []
                    for entry in entries:
                        full = os.path.join(path, entry)
                        if os.path.isdir(full) or full.endswith(".py"):
                            insert_node(node_id, full)

            insert_node("", folder)
            # Open the root
            roots = self.file_tree.get_children()
            if roots:
                self.file_tree.item(roots[0], open=True)

    def _on_tree_double_click(self, event):
        item = self.file_tree.identify_row(event.y)
        if not item:
            return
        path = self.file_tree.set(item, "fullpath") or self.file_tree.item(item, "text")
        if os.path.isdir(path):
            self.file_tree.item(item, open=(not self.file_tree.item(item, "open")))
            return
        if os.path.isfile(path) and path.endswith(".py"):
            try:
                with open(path, "r", encoding="utf-8") as f:
                    content = f.read()
                title = os.path.basename(path)
                # Reuse tab if already open
                for frame, data in self.tabs.items():
                    if data.get("filepath") == path:
                        self.notebook.select(frame)
                        data["text"].delete("1.0", tk.END)
                        data["text"].insert("1.0", content)
                        self.schedule_highlight()
                        self.status["text"] = f"Re-opened: {path}"
                        return
                self._new_tab(title, filepath=path, content=content)
                self.status["text"] = f"Opened: {path}"
            except Exception as e:
                messagebox.showerror("Open File Error", str(e))

    # ---------------------- Tabs ----------------------
    def _init_tab_context_menu(self):
        self.tab_menu = tk.Menu(self, tearoff=0)
        self.tab_menu.add_command(label="Close", command=self._close_current_tab)
        self.tab_menu.add_command(label="Close Others", command=self._close_other_tabs)
        self.tab_menu.add_command(label="Close All", command=self._close_all_tabs)

    def _show_tab_menu(self, event):
        # Only show when clicking on a tab area
        x, y = event.x, event.y
        elem = self.notebook.identify(x, y)
        if "label" in elem:
            self.notebook.select(self.notebook.index(f"@{x},{y}"))
            self.tab_menu.tk_popup(event.x_root, event.y_root)

    def _close_current_tab(self):
        current = self.notebook.select()
        if not current:
            return
        frame = self.nametowidget(current)
        # Prevent closing the last tab; instead clear it
        if len(self.tabs) == 1:
            data = self.tabs[frame]
            data["text"].delete("1.0", tk.END)
            data["filepath"] = None
            self.notebook.tab(current, text="Untitled")
            return
        self.notebook.forget(frame)
        self.tabs.pop(frame, None)

    def _close_other_tabs(self):
        current = self.notebook.select()
        for frame in list(self.tabs.keys()):
            if str(frame) != current:
                self.notebook.forget(frame)
                self.tabs.pop(frame, None)

    def _close_all_tabs(self):
        for frame in list(self.tabs.keys()):
            self.notebook.forget(frame)
            self.tabs.pop(frame, None)
        self._new_tab("Untitled")

    def _bind_editor_events(self, text_widget, line_numbers):
        def on_activity(event):
            # Update line numbers
            self._update_line_numbers(line_numbers, text_widget)
            # Schedule syntax highlight
            self.schedule_highlight()

        for ev in ("<KeyRelease>", "<ButtonRelease-1>", "<MouseWheel>", "<Configure>"):
            text_widget.bind(ev, on_activity, add="+")

    def _new_tab(self, title, filepath=None, content=""):
        frame = ttk.Frame(self.notebook)

        # Shared Font object (important for zoom)
        editor_font = font.Font(
            family="Consolas" if sys.platform == "win32" else "Monaco", size=11
        )

        # Respect global wrap option
        wrap_mode = "word" if self.options.get("word_wrap", False) else "none"

        # Main editor
        text_widget = tk.Text(
            frame, wrap=wrap_mode, font=editor_font, undo=True, maxundo=-1
        )
        text_widget.grid(row=0, column=1, sticky="nsew")

        # Line numbers (Canvas)
        line_numbers = LineNumberCanvas(frame, text_widget, width=40, bg="#f0f0f0")
        line_numbers.font = editor_font  # Share same Font
        line_numbers.line_height = editor_font.metrics("linespace")
        line_numbers.grid(row=0, column=0, sticky="ns")
        line_numbers.redraw()

        # Scrollbars
        yscroll = ttk.Scrollbar(frame, orient="vertical")
        yscroll.grid(row=0, column=2, sticky="ns")
        xscroll = ttk.Scrollbar(frame, orient="horizontal", command=text_widget.xview)
        xscroll.grid(row=1, column=1, sticky="ew")

        # Sync scroll
        def on_vertical_scroll(*args):
            text_widget.yview(*args)
            line_numbers.redraw()

        yscroll.config(command=on_vertical_scroll)
        text_widget.configure(
            yscrollcommand=lambda *args: (yscroll.set(*args), line_numbers.redraw()),
            xscrollcommand=xscroll.set,
        )

        # Layout weights
        frame.rowconfigure(0, weight=1)
        frame.columnconfigure(1, weight=1)

        # Insert initial content
        if content:
            text_widget.insert("1.0", content)

        # Bind updates
        for ev in ("<KeyRelease>", "<ButtonRelease-1>", "<MouseWheel>", "<Configure>"):
            text_widget.bind(
                ev,
                lambda e: (line_numbers.redraw(), self.schedule_highlight()),
                add="+",
            )

        text_widget.bind("<Return>", self.handle_auto_indent, add="+")
        text_widget.bind("<Tab>", self.handle_tab, add="+")
        text_widget.bind("<Shift-Tab>", self.handle_shift_tab, add="+")

        # Register tab
        self.notebook.add(frame, text=title)
        self.tabs[frame] = {
            "text": text_widget,
            "filepath": filepath,
            "font": editor_font,  # keep reference to Font
            "line_numbers": line_numbers,
        }
        self.notebook.select(frame)

        # Apply theme and highlight
        self._apply_theme_to_widget(text_widget)
        line_numbers.redraw()
        self.schedule_highlight()

    def _sync_scroll(self, line_numbers, scrollbar, first, last):
        """Called by text widget scroll: update line numbers and scrollbar."""
        line_numbers.yview_moveto(first)
        scrollbar.set(first, last)

    def _scroll_both(self, line_numbers, text_widget, *args):
        """Called by scrollbar: scroll both text and line numbers."""
        text_widget.yview(*args)
        line_numbers.yview(*args)

    def _update_line_numbers_font(self, line_numbers, editor_font):
        """
        Ensure the line_numbers Text widget uses the same font as the editor.
        This function is defensive: it accepts either a tkinter.font.Font instance
        or a font description (tuple/string) and applies a safe font value to the
        'line_numbers' Text widget so Tk doesn't attempt to call font.Font.config
        on the wrong object.
        """
        try:
            # If we received a font.Font object, pull family/size and pass a tuple.
            if isinstance(editor_font, font.Font):
                fam = editor_font.actual("family")
                sz = editor_font.actual("size")
                # Pass a simple (family, size) tuple to avoid edge-cases.
                line_numbers.config(font=(fam, sz))
            else:
                # editor_font might already be a tuple or string acceptable by Tk.
                line_numbers.config(font=editor_font)
        except Exception as e:
            # Don't crash the app; log to console for debugging.
            try:
                self._append_console(f"[Line-number font update error: {e}]\n")
            except Exception:
                pass

    def _get_current_editor(self):
        current_tab = self.notebook.select()
        if not current_tab:
            return None, None
        frame = self.nametowidget(current_tab)
        data = self.tabs.get(frame)
        if not data:
            return None, None
        return data["text"], data

    def _on_scroll(self, text_widget, line_numbers, *args):
        """Scroll both text widget and line numbers immediately."""
        text_widget.yview(*args)  # scroll text
        line_numbers.yview(*args)  # scroll line numbers
        self._update_line_numbers(line_numbers, text_widget)  # redraw numbers

    def _update_line_numbers(self, line_numbers, text_widget):
        """Update line numbers to match the currently visible lines."""
        line_numbers.config(state="normal")
        line_numbers.delete("1.0", tk.END)

        # Get the index of the first visible line
        first_visible = text_widget.index("@0,0")
        last_visible = text_widget.index(f"@0,{text_widget.winfo_height()}")

        first_line = int(first_visible.split(".")[0])
        last_line = int(last_visible.split(".")[0])

        lines = "\n".join(str(i) for i in range(first_line, last_line + 1))
        line_numbers.insert("1.0", lines)
        line_numbers.config(state="disabled")

    def _on_yscroll(self, line_numbers, text_widget, *args):
        """Called by scrollbar: scroll both text and line numbers"""
        text_widget.yview(*args)
        line_numbers.yview(*args)

    # ---------------------- Editing helpers ----------------------
    def _toggle_line_numbers(self):
        """Show/hide line number widgets in all open tabs (global toggle)."""
        show = bool(self.show_line_numbers_var.get())
        for frame, data in self.tabs.items():
            ln = data.get("line_numbers")
            if not ln:
                continue
            try:
                if show:
                    # restore to its previous grid; if that fails, place it explicitly
                    try:
                        ln.grid()
                    except Exception:
                        ln.grid(row=0, column=0, sticky="ns")
                else:
                    ln.grid_remove()
            except Exception:
                # defensive: don't crash on weird states
                try:
                    self._append_console("[Line-number toggle failed for a tab]\n")
                except Exception:
                    pass
        # Ensure the visible tab layout refreshes
        try:
            self.update_idletasks()
        except Exception:
            pass

    def _show_advanced_settings(self):
        advanced_window = tk.Toplevel(self)
        advanced_window.title("Advanced Settings")
        advanced_window.geometry("400x400")

        notebook = ttk.Notebook(advanced_window)
        notebook.pack(expand=True, fill='both')

        # Вкладки с различными категориями настроек
        general_frame = ttk.Frame(notebook)
        editor_frame = ttk.Frame(notebook)
        appearance_frame = ttk.Frame(notebook)
        terminal_frame = ttk.Frame(notebook)

        notebook.add(general_frame, text="General")
        notebook.add(editor_frame, text="Editor")
        notebook.add(appearance_frame, text="Appearance")
        notebook.add(terminal_frame, text="Terminal")

        # Примеры элементов управления на первой вкладке (General)
        autosave_var = tk.IntVar()
        tk.Checkbutton(general_frame, text="Autosave every minute", variable=autosave_var).grid(sticky="W")

        # Другие вкладки аналогичным образом содержат чекбоксы, переключатели и прочие виджеты
        # Например, ползунки для изменения размера шрифта, выпадающие списки цветов, выборовые кнопки для типа оболочки и т.п.

        # Окончательная кнопка подтверждения настроек
        button_frame = ttk.Frame(advanced_window)
        button_frame.pack(fill="x", pady=10)
        ok_button = ttk.Button(button_frame, text="OK", command=advanced_window.destroy)
        cancel_button = ttk.Button(button_frame, text="Cancel", command=advanced_window.destroy)
        ok_button.pack(side="right", padx=5)
        cancel_button.pack(side="right", padx=5)

    def _toggle_word_wrap(self):
        self.options["word_wrap"] = not self.options["word_wrap"]
        wrap_mode = "word" if self.options["word_wrap"] else "none"

        for data in self.tabs.values():
            data["text"].config(wrap=wrap_mode)

    def handle_auto_indent(self, event):
        """
        Smart newline:
        - Keeps the same leading whitespace as the current line.
        - If the text before the cursor ends with ':' (common in Python),
        add an extra 4 spaces.
        """
        text_widget = event.widget
        # compute current line index
        insert_index = text_widget.index("insert")
        try:
            line_no = int(insert_index.split(".")[0])
        except Exception:
            line_no = 1

        line_start = f"{line_no}.0"
        # text of the current line
        line_text = text_widget.get(line_start, f"{line_no}.end")
        # whitespace at start of the line
        m = re.match(r"[ \t]*", line_text)
        indent = m.group(0) if m else ""

        # check the text *before* cursor (so Enter in the middle works)
        before_cursor = text_widget.get(line_start, "insert")
        if before_cursor.rstrip().endswith(":"):
            indent = indent + " " * 4

        # Insert newline + indent and keep cursor after the indent
        text_widget.insert("insert", "\n" + indent)
        return "break"

    def handle_tab_to_spaces(self, event):
        event.widget.insert(tk.INSERT, " " * 4)
        return "break"

    def handle_tab(self, event):
        """
        Tab behavior:
        - If text is selected: indent every selected line by 4 spaces.
        - If no selection: insert 4 spaces at cursor.
        """
        text_widget = event.widget
        try:
            sel_start = text_widget.index("sel.first")
            sel_end = text_widget.index("sel.last")
        except tk.TclError:
            sel_start = None

        if sel_start:
            # compute selection line range
            start_line = int(sel_start.split(".")[0])
            end_line = int(sel_end.split(".")[0])
            # If selection ends exactly at column 0 of the next line, don't include that line
            end_col = int(sel_end.split(".")[1])
            if end_col == 0 and end_line > start_line:
                end_line -= 1

            # Insert 4 spaces at start of each selected line (top-down)
            for ln in range(start_line, end_line + 1):
                text_widget.insert(f"{ln}.0", " " * 4)

            # Reselect the (now-indented) lines — select full lines to keep it stable
            text_widget.tag_remove("sel", "1.0", tk.END)
            text_widget.tag_add("sel", f"{start_line}.0", f"{end_line}.end")
        else:
            # simple insert of 4 spaces
            text_widget.insert("insert", " " * 4)

        return "break"

    def handle_shift_tab(self, event):
        """
        Shift+Tab (unindent):
        - If selection: for each selected line, remove one leading tab or up to 4 leading spaces.
        - If no selection: remove leading tab or up to 4 spaces on the current line.
        """
        text_widget = event.widget
        try:
            sel_start = text_widget.index("sel.first")
            sel_end = text_widget.index("sel.last")
        except tk.TclError:
            sel_start = None

        if sel_start:
            start_line = int(sel_start.split(".")[0])
            end_line = int(sel_end.split(".")[0])
            end_col = int(sel_end.split(".")[1])
            if end_col == 0 and end_line > start_line:
                end_line -= 1

            for ln in range(start_line, end_line + 1):
                line_start_idx = f"{ln}.0"
                line_text = text_widget.get(line_start_idx, f"{ln}.end")
                if line_text.startswith("\t"):
                    # remove one tab character
                    text_widget.delete(line_start_idx, f"{ln}.0 + 1c")
                else:
                    # remove up to 4 leading spaces
                    m = re.match(r" {1,4}", line_text)
                    if m:
                        removed = m.end()
                        text_widget.delete(line_start_idx, f"{ln}.0 + {removed}c")

            # Reselect the (now-unindented) lines
            text_widget.tag_remove("sel", "1.0", tk.END)
            text_widget.tag_add("sel", f"{start_line}.0", f"{end_line}.end")
        else:
            # Unindent current line
            insert_index = text_widget.index("insert")
            line_no = int(insert_index.split(".")[0])
            line_start_idx = f"{line_no}.0"
            line_text = text_widget.get(line_start_idx, f"{line_no}.end")
            if line_text.startswith("\t"):
                text_widget.delete(line_start_idx, f"{line_no}.0 + 1c")
            else:
                m = re.match(r" {1,4}", line_text)
                if m:
                    removed = m.end()
                    text_widget.delete(line_start_idx, f"{line_no}.0 + {removed}c")

        return "break"

    # ---------------------- Highlighting ----------------------
    def _ensure_highlight_patterns(self):
        """Compile regexes once for performance and reuse."""
        if hasattr(self, "_hl_patterns"):
            return

        # Use the globals you already defined (KEYWORDS, COMMENT, STRING, etc.)
        # compile with flags suitable for each pattern
        self._hl_patterns = {
            "string": re.compile(STRING, re.DOTALL | re.MULTILINE),
            "comment": re.compile(COMMENT),
            "keyword": re.compile(KEYWORDS),
            "number": re.compile(NUMBERS),
            "builtin": re.compile(BUILTINS),
            "function": re.compile(FUNCTION_DEF, re.MULTILINE),
            "class": re.compile(CLASS_DEF, re.MULTILINE),
            "decorator": re.compile(DECORATOR),
        }

    def highlight_syntax(self):
        text_widget, _ = self._get_current_editor()
        if not text_widget:
            return

        code = text_widget.get("1.0", tk.END)

        # remove old tags
        for tag in (
            "keyword",
            "comment",
            "string",
            "number",
            "builtin",
            "function",
            "class",
            "decorator",
        ):
            text_widget.tag_remove(tag, "1.0", tk.END)

        try:
            # Tokenizer approach (precise but strict)
            tokens = tokenize.generate_tokens(io.StringIO(code).readline)
            for tok_type, tok_str, start, end, _ in tokens:
                if tok_type == token.NAME and tok_str in self.python_keywords:
                    tag = "keyword"
                elif tok_type == token.NAME and tok_str in self.python_builtins:
                    tag = "builtin"
                elif tok_type == token.STRING:
                    tag = "string"
                elif tok_type == token.NUMBER:
                    tag = "number"
                elif tok_type == token.COMMENT:
                    tag = "comment"
                else:
                    tag = None

                if tag:
                    start_index = f"{start[0]}.{start[1]}"
                    end_index = f"{end[0]}.{end[1]}"
                    text_widget.tag_add(tag, start_index, end_index)

        except (tokenize.TokenError, IndentationError, SyntaxError):
            # 🚑 Fallback: regex highlighter (safe even with broken code)
            for pattern, tag in [
                (
                    r"\b(?:def|class|if|else|elif|while|for|try|except|return|import|from|as|with|pass|break|continue|lambda|yield|raise|in|is|not|and|or)\b",
                    "keyword",
                ),
                (r"#.*", "comment"),
                (r"(\"[^\"]*\"|'[^']*')", "string"),
                (r"\b\d+(\.\d+)?\b", "number"),
            ]:
                for match in re.finditer(pattern, code):
                    start, end = match.span()
                    start_index = text_widget.index(f"1.0 + {start}c")
                    end_index = text_widget.index(f"1.0 + {end}c")
                    text_widget.tag_add(tag, start_index, end_index)

    def _highlight_heartbeat(self):
        self.schedule_highlight()
        self.after(1000, self._highlight_heartbeat)  # run every 1s

    def schedule_highlight(self, event=None):
        """Cancel any pending highlight and schedule a new one after HIGHLIGHT_DELAY ms."""
        try:
            if getattr(self, "highlight_after_id", None):
                self.after_cancel(self.highlight_after_id)
        except Exception:
            pass
        try:
            self.highlight_after_id = self.after(HIGHLIGHT_DELAY, self.highlight_syntax)
        except Exception:
            # defensive fallback: call directly
            try:
                self.highlight_syntax()
            except Exception:
                pass

    # ---------------------- Theming ----------------------
    def _append_console(self, text):
        self.after(0, lambda: self._append_console_safe(text))

    def _append_console_safe(self, text):
        self.console.config(state="normal")
        self.console.insert(tk.END, text)
        self.console.see(tk.END)
        self.console.config(state="disabled")

    def _apply_theme_to_widget(self, text_widget):
        theme = self.theme
        text_widget.config(bg=theme["background"], fg=theme["foreground"])
        text_widget.tag_configure("keyword", foreground=theme.get("keyword", "#0000FF"))
        text_widget.tag_configure("comment", foreground=theme.get("comment", "#008000"))
        text_widget.tag_configure("string", foreground=theme.get("string", "#BA2121"))
        text_widget.tag_configure("number", foreground=theme.get("number", "#FF00FF"))
        text_widget.tag_configure("builtin", foreground=theme.get("builtin", "#FF8C00"))
        text_widget.tag_configure(
            "function", foreground=theme.get("function", "#FFD700")
        )
        text_widget.tag_configure("class", foreground=theme.get("class", "#00CED1"))
        text_widget.tag_configure(
            "decorator", foreground=theme.get("decorator", "#FF1493")
        )

    def _apply_theme(self):
        theme = self.theme
        self.console.config(bg=theme["console_bg"], fg=theme["console_fg"])
        self.console_input.config(bg=theme["console_bg"], fg=theme["console_fg"])
        for data in self.tabs.values():
            self._apply_theme_to_widget(data["text"])

    def toggle_theme(self):
        self.theme = DARK_THEME if self.theme == LIGHT_THEME else LIGHT_THEME
        self._apply_theme()

    def zoom(self, delta):
        text_widget, data = self._get_current_editor()
        if not text_widget or not data:
            return

        # Ensure we have a Font object in data["font"]
        f = data.get("font")
        if not isinstance(f, font.Font):
            try:
                # try to create a Font from the Text widget's current font
                f = font.Font(font=text_widget.cget("font"))
            except Exception:
                f = font.Font(
                    family="Consolas" if sys.platform == "win32" else "Monaco", size=11
                )
            data["font"] = f

        # read current size robustly
        try:
            current_size = int(f.cget("size"))
        except Exception:
            current_size = int(f.actual().get("size", 11))

        new_size = max(6, current_size + int(delta))

        # update the Font object — this updates the Text automatically (named fonts)
        try:
            f.configure(size=new_size)
        except Exception as e:
            # fallback: set tuple font on text widget only
            try:
                fam = f.actual().get(
                    "family", "Consolas" if sys.platform == "win32" else "Monaco"
                )
                text_widget.config(font=(fam, new_size))
            except Exception:
                try:
                    self._append_console(f"[Zoom error: {e}]\n")
                except Exception:
                    pass

        # Ensure the text widget explicitly uses the Font object (defensive)
        try:
            text_widget.config(font=f)
        except Exception:
            pass

        # Update line numbers: do NOT call ln.config(font=...). Use set_font or assign the Font object
        ln = data.get("line_numbers")
        if ln:
            try:
                # prefer the setter which will compute line_height and redraw
                if hasattr(ln, "set_font"):
                    ln.set_font(f)
                else:
                    # defensive: ensure ln.font is a Font object
                    if not isinstance(getattr(ln, "font", None), font.Font):
                        try:
                            ln.font = font.Font(font=getattr(ln, "font", f))
                        except Exception:
                            ln.font = f
                    ln.font = f
                    ln.line_height = int(f.metrics("linespace") or 1)
                    ln.redraw()
            except Exception as e:
                try:
                    self._append_console(f"[Zoom apply error (line numbers): {e}]\n")
                except Exception:
                    pass

    # ---------------------- Run/Stop ----------------------
    def _send_input(self, event):
        user_input = self.console_input.get("1.0", tk.END)
        self.console_input.delete("1.0", tk.END)
        if user_input.strip():
            if not user_input.endswith("\n"):
                user_input += "\n"
            with self.proc_lock:
                if self.process and self.process.poll() is None:
                    try:
                        if self.process.stdin:
                            self.process.stdin.write(user_input)
                            self.process.stdin.flush()
                        else:
                            self._append_console("[Process has no stdin]\n")
                    except Exception as e:
                        self._append_console(f"[Input Error] {e}\n")
                else:
                    self._append_console("[No running process]\n")
        return "break"

    def run_code(self):
        # Prevent launching multiple processes concurrently
        with self.proc_lock:
            if self.process and self.process.poll() is None:
                self._append_console("[A script is already running]\n")
                return

        interpreter = self.python_interpreter or PYTHON
        if not interpreter or not os.path.isfile(interpreter):
            self._append_console("[Error] No system Python interpreter found.\n")
            self._append_console(
                "Please install Python from https://www.python.org/downloads/\n"
            )
            self._append_console(
                "Or set a custom interpreter in the Interpreter menu\n"
            )
            return

        text_widget, tab_data = self._get_current_editor()
        if not text_widget:
            self._append_console("[No editor available]\n")
            return

        # Save current buffer to file (existing filepath or temporary file)
        filepath = tab_data.get("filepath")
        if filepath:
            try:
                with open(filepath, "w", encoding="utf-8") as f:
                    f.write(text_widget.get("1.0", tk.END))
            except Exception as e:
                messagebox.showerror("Save Error", str(e))
                return
            path = filepath
        else:
            with tempfile.NamedTemporaryFile(
                delete=False, suffix=".py", mode="w", encoding="utf-8"
            ) as f:
                f.write(text_widget.get("1.0", tk.END))
                path = f.name
                self.tempfile_path = path

        self._append_console(f"Running: {path}\n")
        self.status["text"] = "Running"

        def target():
            try:
                start_new_session = sys.platform != "win32"
                with self.proc_lock:
                    try:
                        # On Windows, prevent console windows for subprocesses
                        popen_kwargs = dict(
                            stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE,
                            stdin=subprocess.PIPE,
                            text=True,
                            bufsize=1,
                        )
                        if sys.platform == "win32":
                            popen_kwargs["creationflags"] = subprocess.CREATE_NO_WINDOW
                        else:
                            # create new session on POSIX so signals don't conflict
                            popen_kwargs["start_new_session"] = True

                        self.process = subprocess.Popen(
                            [interpreter, "-u", path], **popen_kwargs
                        )
                    except Exception as e:
                        self._append_console(f"Failed to start process: {e}\n")
                        self.after(0, lambda: self.status.config(text="Ready"))
                        self.process = None
                        return

            except Exception as e:
                self._append_console(f"Failed to start process: {e}\n")
                self.after(0, lambda: self.status.config(text="Ready"))
                with self.proc_lock:
                    self.process = None
                return

            def stream_reader(stream):
                try:
                    for line in iter(stream.readline, ""):
                        if line == "":
                            break
                        self.output_queue.put(line)
                finally:
                    try:
                        stream.close()
                    except Exception:
                        pass

            threading.Thread(
                target=stream_reader, args=(self.process.stdout,), daemon=True
            ).start()
            threading.Thread(
                target=stream_reader, args=(self.process.stderr,), daemon=True
            ).start()

            self.process.wait()
            self.output_queue.put(
                f"\n[Process exited with return code {self.process.returncode}]\n"
            )

            with self.proc_lock:
                self.process = None

            if self.tempfile_path:
                try:
                    os.remove(self.tempfile_path)
                except Exception:
                    pass
                finally:
                    self.tempfile_path = None

            self.after(0, lambda: self.status.config(text="Ready"))

        threading.Thread(target=target, daemon=True).start()
        self.after(80, self._drain_output)

    def stop_code(self):
        with self.proc_lock:
            if self.process and self.process.poll() is None:
                try:
                    if sys.platform == "win32":
                        self.process.terminate()
                    else:
                        os.killpg(os.getpgid(self.process.pid), signal.SIGTERM)
                    self._append_console("\n[Process terminated]\n")
                except Exception:
                    try:
                        self.process.terminate()
                        self._append_console("\n[Process terminated (fallback)]\n")
                    except Exception as e2:
                        self._append_console(f"\n[Failed to terminate process] {e2}\n")
            else:
                self._append_console("[No running process]\n")

    def _drain_output(self):
        drained_any = False
        try:
            while True:
                line = self.output_queue.get_nowait()
                self._append_console(line)
                drained_any = True
        except queue.Empty:
            pass
        with self.proc_lock:
            proc_alive = bool(self.process and self.process.poll() is None)
        if proc_alive or not self.output_queue.empty():
            self.after(80 if drained_any else 120, self._drain_output)
        else:
            self.after(0, lambda: self.status.config(text="Ready"))

    # ---------------------- App lifecycle ----------------------
    def _on_close(self):
        try:
            self.stop_code()
            self._save_config()
        except Exception:
            pass
        self.destroy()


if __name__ == "__main__":
    app = SimplePythonIDE()
    app.mainloop()

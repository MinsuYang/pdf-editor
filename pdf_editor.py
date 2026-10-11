"""
PDF 편집기 v2.2
made by 양민수

필요 라이브러리:
    pip install pypdf pymupdf tkinterdnd2 pillow

exe 변환:
    pyinstaller --onefile --windowed --name PDF편집기 --icon=icon.ico pdf_editor.py
"""

import os, re, copy, threading
import tkinter as tk
from tkinter import ttk, filedialog, messagebox, simpledialog
from PIL import Image, ImageTk

try:
    from tkinterdnd2 import DND_FILES, TkinterDnD
    DND_AVAILABLE = True
except ImportError:
    DND_AVAILABLE = False

try:
    import fitz
    FITZ_AVAILABLE = True
except ImportError:
    FITZ_AVAILABLE = False

from pypdf import PdfReader, PdfWriter

# ── 제한값 ────────────────────────────────────────────────────
MAX_MB    = 100
MAX_PAGES = 300

# ── 색상 ──────────────────────────────────────────────────────
BG       = "#F7F7F5"
CARD_BG  = "#FFFFFF"
BORDER   = "#E0DED8"
GREEN    = "#1D9E75"
GREEN_LT = "#E1F5EE"
GREEN_DK = "#0F6E56"
RED_LT   = "#FCEBEB"
RED      = "#A32D2D"
TEXT_PRI = "#1A1A18"
TEXT_SEC = "#5F5E5A"
TEXT_TER = "#888780"
GRAY_LT  = "#F1EFE8"
SEL_BD   = "#1D9E75"

def make_card(parent, **kw):
    f = tk.Frame(parent, bg=CARD_BG, **kw)
    f.configure(highlightbackground=BORDER, highlightthickness=1)
    return f


class PDFEditorApp:
    # ═══════════════════════════════════════════════════════════
    # 초기화
    # ═══════════════════════════════════════════════════════════
    def __init__(self, root):
        self.root = root
        self.root.title("PDF 편집기  v2.2")
        self.root.configure(bg=BG)
        self.root.resizable(True, True)
        self.root.minsize(900, 580)

        # ── 문서 상태 ──
        self.pdf_path    = None
        self.total_pages = 0
        self.output_dir  = os.path.expanduser("~")
        self.page_order  = []   # global_idx 순서
        self.rotations   = {}   # {global_idx: deg}
        self.selected    = set()
        self.cut_points  = set()
        self.split_mode  = "equal"
        self.split_active = False
        # global_idx → (file_path, local_idx) 완전 직접 매핑
        self._page_map   = {}

        # ── Undo 스택 ──
        self.undo_stack  = []   # 최대 20

        # ── 썸네일 ──
        self.thumb_photos = []
        self.thumb_cache  = {}  # {global_idx: PIL.Image 원본}
        self.thumb_size   = 130  # 기본 크기
        self._thumb_cells = {}  # {pos: cell_frame}
        self._thumb_pos_map = []  # [(pos, gidx, cell)]

        # ── 드래그 상태 ──
        self._drag_start_root = None
        self._drag_active     = False
        self._drag_pages_buf  = []
        self._drag_insert_pos = -1
        self._last_click_time = 0
        self._last_click_idx  = None
        self._single_click_job = None

        self._build_ui()

    # ═══════════════════════════════════════════════════════════
    # UI 구성
    # ═══════════════════════════════════════════════════════════
    def _build_ui(self):
        root = self.root

        # ── 메뉴바 ──
        mbar = tk.Frame(root, bg=CARD_BG,
                        highlightbackground=BORDER, highlightthickness=1)
        mbar.pack(fill="x")
        tk.Label(mbar, text="✂  PDF 편집기",
                 font=("Malgun Gothic", 13, "bold"),
                 bg=CARD_BG, fg=TEXT_PRI).pack(side="left", padx=12, pady=5)
        tk.Button(mbar, text="도움말",
                  font=("Malgun Gothic", 10),
                  bg=CARD_BG, fg=TEXT_SEC, relief="flat", bd=0, padx=8,
                  command=self._show_help).pack(side="left")
        tk.Label(mbar, text="made by 양민수",
                 font=("Malgun Gothic", 10, "bold"),
                 bg=CARD_BG, fg=TEXT_SEC).pack(side="right", padx=12)

        # ── 탭바 ──
        tbar = tk.Frame(root, bg=CARD_BG,
                        highlightbackground=BORDER, highlightthickness=1)
        tbar.pack(fill="x")
        self.tab_btns = {}
        self.panels   = {}
        for tid, lbl in [("edit", "페이지 편집")]:
            btn = tk.Label(tbar, text=lbl,
                           font=("Malgun Gothic", 10, "bold"),
                           bg=CARD_BG, fg=GREEN, padx=16, pady=7,
                           cursor="hand2")
            btn.pack(side="left")
            btn.bind("<Button-1>", lambda e, t=tid: self._switch_tab(t))
            self.tab_btns[tid] = btn

        # ── 편집 패널 ──
        ep = tk.Frame(root, bg=BG)
        ep.pack(fill="both", expand=True)
        self.panels["edit"] = ep
        self._build_edit_tab(ep)

    def _build_edit_tab(self, parent):
        parent.columnconfigure(1, weight=1)
        parent.rowconfigure(0, weight=1)

        # ── 왼쪽 패널 ──
        left = make_card(parent)
        left.grid(row=0, column=0, sticky="nsew", padx=(8,4), pady=8)
        left.configure(width=185)

        self._sl(left, "파일")
        for icon, txt, cmd in [
            ("📂", "PDF 열기",         self._open_pdf),
            ("➕", "파일 추가 (병합)", self._add_pdf),
            ("💾", "저장",             self._save_pdf),
            ("📋", "다른 이름으로 저장", self._save_as_pdf),
        ]:
            self._tb(left, icon, txt, cmd)

        self._sl(left, "페이지 작업")
        self.tool_vars = {}
        btn_sp = self._tb(left, "✂", "분할 모드", self._toggle_split_mode)
        self.tool_vars["split"] = btn_sp
        self._tb(left, "📄", "추출 (선택 페이지)", self._extract_selected)
        self._tb(left, "🗑", "삭제 (선택 페이지)", self._delete_selected)

        # ── 분할 패널 ──
        self.split_panel = tk.Frame(left, bg=CARD_BG)
        self._sl(self.split_panel, "분할 방식")
        mr = tk.Frame(self.split_panel, bg=CARD_BG)
        mr.pack(fill="x", padx=8, pady=(0,6))
        self.split_mode_btns = {}
        for mid, lbl in [("equal","등분"),("free","자유"),("click","클릭")]:
            b = tk.Label(mr, text=lbl, font=("Malgun Gothic", 9),
                         bg=GRAY_LT, fg=TEXT_SEC, padx=6, pady=3,
                         cursor="hand2", relief="solid", bd=1)
            b.pack(side="left", fill="x", expand=True, padx=1)
            b.bind("<Button-1>", lambda e, m=mid: self._set_split_mode(m))
            self.split_mode_btns[mid] = b

        self.eq_frame = tk.Frame(self.split_panel, bg=CARD_BG)
        self.eq_frame.pack(fill="x", padx=8)
        tk.Label(self.eq_frame, text="페이지/파일",
                 font=("Malgun Gothic", 8), bg=CARD_BG, fg=TEXT_TER).pack(anchor="w")
        self.eq_entry = tk.Entry(self.eq_frame, width=8,
                                 font=("Malgun Gothic", 10), relief="solid", bd=1)
        self.eq_entry.insert(0, "10")
        self.eq_entry.pack(fill="x", pady=(2,4))
        tk.Label(self.eq_frame, text="예: 10 → 10페이지씩 자동 분할",
                 font=("Malgun Gothic", 8), bg=CARD_BG, fg=TEXT_TER,
                 wraplength=155, justify="left").pack(anchor="w", pady=(0,6))

        self.free_frame = tk.Frame(self.split_panel, bg=CARD_BG)
        tk.Label(self.free_frame, text="구간 직접 입력",
                 font=("Malgun Gothic", 8), bg=CARD_BG, fg=TEXT_TER).pack(anchor="w", padx=8)
        self.free_entry = tk.Entry(self.free_frame, font=("Malgun Gothic", 10),
                                   relief="solid", bd=1)
        self.free_entry.pack(fill="x", padx=8, pady=(2,2))
        self.free_err = tk.Label(self.free_frame, text="",
                                 font=("Malgun Gothic", 8), bg=CARD_BG, fg=RED,
                                 wraplength=155, justify="left")
        self.free_err.pack(anchor="w", padx=8)
        tk.Label(self.free_frame,
                 text="예: 3,7,10,5,5\n합계 불일치 시 나머지 자동 추가",
                 font=("Malgun Gothic", 8), bg=CARD_BG, fg=TEXT_TER,
                 wraplength=155, justify="left").pack(anchor="w", padx=8, pady=(2,6))
        self.free_entry.bind("<KeyRelease>", self._validate_free_input)

        self.click_frame = tk.Frame(self.split_panel, bg=CARD_BG)
        tk.Label(self.click_frame,
                 text="썸네일 사이 ✂를 클릭해서\n분할선을 지정하세요",
                 font=("Malgun Gothic", 8), bg=CARD_BG, fg=TEXT_TER,
                 justify="left").pack(anchor="w", padx=8, pady=(0,6))

        # ── 오른쪽 패널 ──
        right = tk.Frame(parent, bg=BG)
        right.grid(row=0, column=1, sticky="nsew", padx=(4,8), pady=8)
        right.rowconfigure(1, weight=1)
        right.columnconfigure(0, weight=1)

        # 툴바
        tb = make_card(right)
        tb.grid(row=0, column=0, sticky="ew", pady=(0,4))
        for txt, cmd in [("전체 선택", self._select_all),
                         ("선택 해제", self._deselect_all),
                         ("앞으로",    self._move_forward),
                         ("뒤로",      self._move_backward)]:
            tk.Button(tb, text=txt, font=("Malgun Gothic", 9),
                      bg=CARD_BG, fg=TEXT_SEC, relief="solid", bd=1,
                      padx=10, pady=4, command=cmd).pack(
                          side="left", padx=(6,2), pady=5)
        tk.Frame(tb, bg=BORDER, width=1).pack(side="left", fill="y", padx=6, pady=5)
        tk.Button(tb, text="선택 삭제",
                  font=("Malgun Gothic", 9), bg=RED_LT, fg=RED,
                  relief="solid", bd=1, padx=10, pady=4,
                  command=self._delete_selected).pack(side="left", padx=2, pady=5)
        tk.Frame(tb, bg=BORDER, width=1).pack(side="left", fill="y", padx=6, pady=5)
        tk.Button(tb, text="↩ 실행 취소",
                  font=("Malgun Gothic", 9), bg=CARD_BG, fg=TEXT_SEC,
                  relief="solid", bd=1, padx=10, pady=4,
                  command=self._undo).pack(side="left", padx=2, pady=5)

        # 캔버스
        cf = make_card(right)
        cf.grid(row=1, column=0, sticky="nsew", pady=(0,4))
        cf.rowconfigure(0, weight=1)
        cf.columnconfigure(0, weight=1)

        self.canvas = tk.Canvas(cf, bg=GRAY_LT, highlightthickness=0)
        vsb = ttk.Scrollbar(cf, orient="vertical",   command=self.canvas.yview)
        hsb = ttk.Scrollbar(cf, orient="horizontal", command=self.canvas.xview)
        self.canvas.configure(yscrollcommand=vsb.set, xscrollcommand=hsb.set)
        self.canvas.grid(row=0, column=0, sticky="nsew")
        vsb.grid(row=0, column=1, sticky="ns")
        hsb.grid(row=1, column=0, sticky="ew")

        self.thumb_frame = tk.Frame(self.canvas, bg=GRAY_LT)
        self.canvas_window = self.canvas.create_window(
            (0,0), window=self.thumb_frame, anchor="nw")
        self.thumb_frame.bind("<Configure>", self._on_frame_cfg)
        self.canvas.bind("<Configure>",      self._on_canvas_cfg)

        # 마우스 휠
        def _mw(e):
            if e.state & 0x0004:
                delta = 1 if e.delta > 0 else -1
                self.thumb_size = max(50, min(250, self.thumb_size + delta * 15))
                self._rebuild_thumbs()
            else:
                self.canvas.yview_scroll(int(-1*(e.delta/120)), "units")
        self.canvas.bind("<MouseWheel>", _mw)
        self.canvas.bind("<Button-4>", lambda e: self.canvas.yview_scroll(-1,"units"))
        self.canvas.bind("<Button-5>", lambda e: self.canvas.yview_scroll(1,"units"))
        self.thumb_frame.bind("<MouseWheel>", _mw)
        # 작업영역 빈 곳(셀이 없는 곳) 클릭 시 선택 해제
        # thumb_frame 의 자식 셀 클릭은 셀이 이벤트 소비 → thumb_frame 까지 전파 안 됨
        self.canvas.bind("<ButtonPress-1>",
                         lambda e: self._deselect_all())
        self.thumb_frame.bind("<ButtonPress-1>",
                              lambda e: self._deselect_all()
                              if str(e.widget) == str(self.thumb_frame) else None)

        # 드래그앤드롭 파일
        if DND_AVAILABLE:
            self.root.drop_target_register(DND_FILES)
            self.root.dnd_bind("<<Drop>>", self._on_file_drop)

        # 상태바
        sb = make_card(right)
        sb.grid(row=2, column=0, sticky="ew")
        tk.Label(sb, text="●", font=("Malgun Gothic",8),
                 bg=CARD_BG, fg=GREEN).pack(side="left", padx=(8,4), pady=4)
        tk.Label(sb, text="Ctrl+휠: 썸네일 크기  |  더블클릭: 페이지 확대",
                 font=("Malgun Gothic",8), bg=CARD_BG, fg=TEXT_TER).pack(side="left")
        self.sel_lbl = tk.Label(sb, text="선택: 0페이지",
                                font=("Malgun Gothic",9), bg=CARD_BG, fg=TEXT_TER)
        self.sel_lbl.pack(side="right", padx=8)

        # 컨텍스트 메뉴
        self.ctx = tk.Menu(self.root, tearoff=0, font=("Malgun Gothic",9))
        self.ctx.add_command(label="90° 시계 방향 회전",  command=lambda: self._rotate_sel(90))
        self.ctx.add_command(label="180° 회전",           command=lambda: self._rotate_sel(180))
        self.ctx.add_command(label="270° 반시계 회전",    command=lambda: self._rotate_sel(270))
        self.ctx.add_separator()
        self.ctx.add_command(label="선택 페이지 추출",    command=self._extract_selected)
        self.ctx.add_separator()
        self.ctx.add_command(label="특정 위치로 이동",    command=self._move_to_pos_dialog)
        self.ctx.add_separator()
        self.ctx.add_command(label="작업영역 내 페이지와 교체", command=self._swap_with_page)
        self.ctx.add_command(label="외부 PDF 페이지로 교체",    command=self._replace_with_external)
        self.ctx.add_separator()
        self.ctx.add_command(label="선택 페이지 삭제",    command=self._delete_selected)

        # 키 바인딩
        self.root.bind("<Control-z>", lambda e: self._undo())
        self.root.bind("<Delete>",    lambda e: self._delete_selected())

        self._set_split_mode("equal")

    # ═══════════════════════════════════════════════════════════
    # 헬퍼
    # ═══════════════════════════════════════════════════════════
    def _sl(self, parent, text):
        tk.Label(parent, text=text, font=("Malgun Gothic",8),
                 bg=CARD_BG, fg=TEXT_TER).pack(anchor="w", padx=10, pady=(8,2))

    def _tb(self, parent, icon, text, cmd):
        f = tk.Frame(parent, bg=CARD_BG)
        f.pack(fill="x", padx=8, pady=1)
        btn = tk.Button(f, text=f"{icon}  {text}",
                        font=("Malgun Gothic",9), bg=CARD_BG, fg=TEXT_SEC,
                        relief="flat", bd=0, anchor="w", padx=6, pady=4, command=cmd)
        btn.pack(fill="x")
        btn.bind("<Enter>", lambda e: btn.configure(bg=GRAY_LT))
        btn.bind("<Leave>", lambda e: btn.configure(bg=CARD_BG))
        return btn

    def _switch_tab(self, tid):
        for t, p in self.panels.items():
            p.pack(fill="both", expand=True) if t==tid else p.pack_forget()

    def _on_frame_cfg(self, e):
        self.canvas.configure(scrollregion=self.canvas.bbox("all"))

    def _on_canvas_cfg(self, e):
        self.canvas.itemconfig(self.canvas_window, width=e.width)
        if self.page_order:
            if hasattr(self, '_resize_job'):
                self.root.after_cancel(self._resize_job)
            self._resize_job = self.root.after(150, self._rebuild_thumbs)

    # ═══════════════════════════════════════════════════════════
    # Undo
    # ═══════════════════════════════════════════════════════════
    def _push_undo(self):
        state = {
            "page_order":  self.page_order[:],
            "rotations":   copy.copy(self.rotations),
            "selected":    copy.copy(self.selected),
            "cut_points":  copy.copy(self.cut_points),
            "_page_map":   copy.copy(self._page_map),
            "thumb_cache": {k: v for k, v in self.thumb_cache.items()},
        }
        self.undo_stack.append(state)
        if len(self.undo_stack) > 20:
            self.undo_stack.pop(0)

    def _undo(self):
        if not self.undo_stack:
            return
        s = self.undo_stack.pop()
        self.page_order  = s["page_order"]
        self.rotations   = s["rotations"]
        self.selected    = s["selected"]
        self.cut_points  = s["cut_points"]
        self._page_map   = s["_page_map"]
        self.thumb_cache = s["thumb_cache"]
        self._rebuild_thumbs()

    # ═══════════════════════════════════════════════════════════
    # 파일 열기 / 병합
    # ═══════════════════════════════════════════════════════════
    def _open_pdf(self):
        p = filedialog.askopenfilename(title="PDF 파일 선택",
            filetypes=[("PDF","*.pdf"),("모든 파일","*.*")])
        if p: self._load_pdf(p, append=False)

    def _add_pdf(self):
        p = filedialog.askopenfilename(title="추가할 PDF 선택",
            filetypes=[("PDF","*.pdf"),("모든 파일","*.*")])
        if p: self._load_pdf(p, append=True)

    def _on_file_drop(self, event):
        raw = event.data.strip()
        paths = re.findall(r'\{([^}]+)\}|([^\s]+)', raw)
        for a, b in paths:
            p = (a or b).strip()
            if not p: continue
            if p.lower().endswith(".pdf") and os.path.isfile(p):
                self._load_pdf(p, append=(self.pdf_path is not None))
            elif os.path.isfile(p):
                self._error_popup("파일 형식 오류",
                                  "PDF 파일만 불러올 수 있습니다!", os.path.basename(p))

    def _load_pdf(self, path, append=False):
        if not os.path.isfile(path): return
        try:
            with open(path,"rb") as f:
                if f.read(5) != b"%PDF-":
                    self._error_popup("파일 형식 오류",
                                      "PDF 파일만 불러올 수 있습니다!", os.path.basename(path))
                    return
        except Exception:
            messagebox.showerror("오류","파일을 읽을 수 없습니다."); return

        size_mb = os.path.getsize(path) / (1024*1024)
        try:
            reader = PdfReader(path)
            n = len(reader.pages)
        except Exception:
            messagebox.showerror("오류","손상된 PDF 파일입니다."); return

        warn = ""
        if size_mb > MAX_MB:
            warn = f"파일 크기가 {size_mb:.0f}MB로 권장 용량({MAX_MB}MB)을 초과합니다.\n처리 속도가 느려질 수 있습니다. 계속하시겠습니까?"
        elif n > MAX_PAGES:
            warn = f"페이지 수가 {n}페이지로 권장 한도({MAX_PAGES}페이지)를 초과합니다.\n처리 속도가 느려질 수 있습니다. 계속하시겠습니까?"
        if warn and not messagebox.askyesno("용량 경고", warn):
            return

        self._push_undo()

        if append and self.pdf_path:
            # 새 global_idx: 현재 _page_map 최대값 + 1
            next_g = (max(self._page_map.keys()) + 1) if self._page_map else 0
            for li in range(n):
                self._page_map[next_g + li] = (path, li)
            self.page_order.extend(range(next_g, next_g + n))
            self.total_pages += n
        else:
            self.pdf_path    = path
            self.total_pages = n
            self.page_order  = list(range(n))
            self.rotations   = {}
            self.selected    = set()
            self.cut_points  = set()
            self.thumb_cache = {}
            self._page_map   = {i: (path, i) for i in range(n)}

        self.output_dir = os.path.dirname(os.path.abspath(path))
        self._rebuild_thumbs()
        threading.Thread(target=self._load_thumbs_bg, daemon=True).start()

    # ═══════════════════════════════════════════════════════════
    # 썸네일 렌더링 (Lazy)
    # ═══════════════════════════════════════════════════════════
    def _load_thumbs_bg(self):
        if not FITZ_AVAILABLE: return
        open_docs = {}
        for gidx, (fpath, lidx) in list(self._page_map.items()):
            if gidx in self.thumb_cache: continue
            if not os.path.isfile(fpath): continue
            try:
                if fpath not in open_docs:
                    open_docs[fpath] = fitz.open(fpath)
                doc = open_docs[fpath]
                if lidx >= len(doc): continue
                pix = doc[lidx].get_pixmap(matrix=fitz.Matrix(0.6, 0.6))
                img = Image.frombytes("RGB", [pix.width, pix.height], pix.samples)
                img.thumbnail((200, 283), Image.LANCZOS)
                self.thumb_cache[gidx] = img
                # 5장마다 UI 갱신
                if len(self.thumb_cache) % 5 == 0:
                    self.root.after(0, self._rebuild_thumbs)
            except Exception:
                pass
        for doc in open_docs.values():
            try: doc.close()
            except: pass
        self.root.after(0, self._rebuild_thumbs)

    def _rebuild_thumbs(self):
        for w in self.thumb_frame.winfo_children():
            w.destroy()
        self.thumb_photos   = []
        self._thumb_cells   = {}
        self._thumb_pos_map = []

        if not self.page_order:
            tk.Label(self.thumb_frame,
                     text="PDF 파일을 열어주세요\n또는 파일을 드래그 앤 드롭하세요",
                     font=("Malgun Gothic",11), bg=GRAY_LT, fg=TEXT_TER
                     ).pack(expand=True, pady=40)
            return

        self.canvas.update_idletasks()
        tw   = self.thumb_size
        th   = int(tw * 1.414)
        pad  = 14
        cols = max(1, (self.canvas.winfo_width() - 20) // (tw + pad))

        # 드롭 인디케이터
        self._drop_line = tk.Frame(self.thumb_frame, bg=GREEN, width=3, height=th+10)
        try: self._drop_line.place_forget()
        except: pass

        for pos, gidx in enumerate(self.page_order):
            row = pos // cols
            col = pos % cols

            # 클릭지정 분할선
            if (self.split_active and self.split_mode == "click"
                    and pos > 0 and col > 0):
                cut_col = col * 2 - 1
                gap = tk.Label(self.thumb_frame,
                               text="✂" if pos in self.cut_points else " ",
                               font=("Malgun Gothic",10), bg=GRAY_LT,
                               fg=RED if pos in self.cut_points else BORDER,
                               cursor="hand2", width=1)
                gap.grid(row=row, column=cut_col, sticky="ns")
                gap.bind("<Button-1>", lambda e, p=pos: self._toggle_cut(p))

            cell_col = col * 2 if (self.split_active and self.split_mode == "click") else col
            is_sel   = gidx in self.selected
            cell = tk.Frame(self.thumb_frame, bg=GRAY_LT,
                            highlightthickness=2,
                            highlightbackground=SEL_BD if is_sel else GRAY_LT,
                            cursor="hand2")
            cell.grid(row=row, column=cell_col, padx=pad//2, pady=pad//2)

            # 이미지
            if gidx in self.thumb_cache:
                img = self.thumb_cache[gidx].copy()
                rot = self.rotations.get(gidx, 0)
                if rot:
                    img = img.rotate(-rot, expand=True)
                img.thumbnail((tw, th), Image.LANCZOS)
                iw, ih = img.size
                if self._drag_active and gidx in set(self._drag_pages_buf):
                    ghost = img.copy().convert("RGBA")
                    ghost.putalpha(80)
                    img = ghost.convert("RGB")
                photo = ImageTk.PhotoImage(img)
                self.thumb_photos.append(photo)
                lbl = tk.Label(cell, image=photo, bg=CARD_BG, width=iw, height=ih)
            else:
                photo = None
                lbl   = tk.Label(cell, text="📄",
                                 font=("Malgun Gothic", max(10, tw//6)),
                                 bg=CARD_BG,
                                 width=max(3, tw//12), height=max(2, th//16))
            lbl.pack(padx=2, pady=2)

            pg_lbl = tk.Label(cell, text=str(pos+1),
                              font=("Malgun Gothic",8), bg=GRAY_LT,
                              fg=GREEN_DK if is_sel else TEXT_TER)
            pg_lbl.pack()

            for w in (cell, lbl, pg_lbl):
                w.bind("<ButtonPress-1>",
                       lambda e, g=gidx, p=pos: self._td_press(e, g, p))
                w.bind("<Button-3>",
                       lambda e, g=gidx: self._on_rclick(e, g))
                w.bind("<B1-Motion>",       lambda e: self._td_motion(e))
                w.bind("<ButtonRelease-1>", lambda e: self._td_release(e))

            self._thumb_cells[pos]   = cell
            self._thumb_pos_map.append((pos, gidx, cell))

        self._update_sel_label()

    # ═══════════════════════════════════════════════════════════
    # 썸네일 이벤트
    # ═══════════════════════════════════════════════════════════
    def _td_press(self, event, gidx, pos):
        """클릭 + 더블클릭 감지 + 드래그 준비
        더블클릭: 같은 페이지 400ms 이내 두 번 → 미리보기
        싱글클릭: rebuild 를 50ms 지연시켜 두 번째 클릭(더블클릭) 감지 우선
        """
        now  = event.time
        last = self._last_click_time
        same = (self._last_click_idx == gidx)

        # 더블클릭 감지
        if now - last < 400 and same:
            # 대기 중인 싱글클릭 job 취소
            if hasattr(self, '_single_click_job') and self._single_click_job:
                self.root.after_cancel(self._single_click_job)
                self._single_click_job = None
            self._last_click_time = 0
            self._preview_page(gidx, pos)
            return

        self._last_click_time = now
        self._last_click_idx  = gidx

        widget = event.widget
        rx = widget.winfo_rootx() + event.x - self.thumb_frame.winfo_rootx()
        ry = widget.winfo_rooty() + event.y - self.thumb_frame.winfo_rooty()
        self._drag_start_root = (rx, ry)
        self._drag_active     = False

        # 선택 처리
        state = event.state
        if state & 0x0001:  # Shift
            if self.selected and pos is not None:
                last_g   = list(self.selected)[-1]
                last_pos = self.page_order.index(last_g)
                mn, mx   = sorted([last_pos, pos])
                self.selected = {self.page_order[i] for i in range(mn, mx+1)}
            else:
                self.selected.add(gidx)
        elif state & 0x0004:  # Ctrl
            if gidx in self.selected: self.selected.discard(gidx)
            else:                     self.selected.add(gidx)
        else:
            if gidx not in self.selected:
                self.selected = {gidx}

        self._drag_pages_buf = list(self.selected) if self.selected else [gidx]

        # 선택 상태 시각 업데이트만 (rebuild 없음 → 깜빡임 없음)
        # 더블클릭 두 번째 press 감지를 위해 50ms 후 실행
        if hasattr(self, '_single_click_job') and self._single_click_job:
            self.root.after_cancel(self._single_click_job)
        self._single_click_job = self.root.after(50, self._update_selection_visuals)

    def _on_rclick(self, event, gidx):
        if gidx not in self.selected:
            self.selected = {gidx}
            self._update_selection_visuals()
        self.ctx.post(event.x_root, event.y_root)

    def _td_motion(self, event):
        if self._drag_start_root is None: return
        widget = event.widget
        rx = widget.winfo_rootx() + event.x - self.thumb_frame.winfo_rootx()
        ry = widget.winfo_rooty() + event.y - self.thumb_frame.winfo_rooty()
        dx = abs(rx - self._drag_start_root[0])
        dy = abs(ry - self._drag_start_root[1])
        if not self._drag_active and (dx > 5 or dy > 5):
            if not self._drag_pages_buf: return
            self._drag_active = True
            # ghost: 드래그 중인 셀들을 반투명하게 (rebuild 없이)
            for pos, gidx, cell in self._thumb_pos_map:
                if gidx in set(self._drag_pages_buf):
                    try: cell.configure(bg="#D0EAE0")
                    except: pass
        if self._drag_active:
            ip = self._get_insert_pos(rx, ry)
            if ip != self._drag_insert_pos:
                self._drag_insert_pos = ip
                self._show_insert_line(ip)

    def _td_release(self, event):
        if not self._drag_active or not self._drag_pages_buf:
            self._drag_active     = False
            self._drag_start_root = None
            return
        ip      = self._drag_insert_pos
        dragged = set(self._drag_pages_buf)
        remain  = [p for p in self.page_order if p not in dragged]
        adj     = sum(1 for p in self._drag_pages_buf
                      if self.page_order.index(p) < ip)
        ri      = max(0, min(ip - adj, len(remain)))
        ordered = [p for p in self.page_order if p in dragged]
        for i, p in enumerate(ordered):
            remain.insert(ri + i, p)
        self._push_undo()
        self.page_order       = remain
        self._drag_active     = False
        self._drag_start_root = None
        self._drag_insert_pos = -1
        if hasattr(self, '_drop_line') and self._drop_line.winfo_exists():
            self._drop_line.place_forget()
        self._rebuild_thumbs()  # 순서 변경이므로 rebuild 필요

    def _get_insert_pos(self, rx, ry):
        if not self._thumb_pos_map: return 0
        best_pos, best_dist = len(self.page_order), float('inf')
        for pos, gidx, cell in self._thumb_pos_map:
            x, y = cell.winfo_x(), cell.winfo_y()
            w, h = cell.winfo_width(), cell.winfo_height()
            if abs(ry - (y + h//2)) < h:
                cx = x + w//2
                if rx <= cx:
                    d = abs(rx - x)
                    if d < best_dist: best_dist, best_pos = d, pos
                else:
                    d = abs(rx - (x+w))
                    if d < best_dist: best_dist, best_pos = d, pos+1
        return best_pos

    def _show_insert_line(self, ip):
        if not self._thumb_pos_map: return
        n = len(self.page_order)
        if n == 0: return
        ref  = min(ip, n-1)
        cell = self._thumb_cells.get(ref)
        if not cell: return
        x, y = cell.winfo_x(), cell.winfo_y()
        h    = cell.winfo_height()
        lx   = x - 3 if ip < n else x + cell.winfo_width() + 1
        self._drop_line.place(x=lx, y=y, width=3, height=h)
        self._drop_line.lift()

    def _toggle_cut(self, pos):
        if not self.split_active: return
        if pos in self.cut_points: self.cut_points.discard(pos)
        else:                      self.cut_points.add(pos)
        self._rebuild_thumbs()

    # ═══════════════════════════════════════════════════════════
    # 선택
    # ═══════════════════════════════════════════════════════════
    def _select_all(self):
        self.selected = set(self.page_order)
        self._update_selection_visuals()

    def _deselect_all(self):
        self.selected.clear()
        self._update_selection_visuals()

    def _update_sel_label(self):
        self.sel_lbl.configure(text=f"선택: {len(self.selected)}페이지")

    def _update_selection_visuals(self):
        """rebuild 없이 선택 테두리/색상만 업데이트 — 깜빡임 없음"""
        if not hasattr(self, '_thumb_pos_map') or not self._thumb_pos_map:
            return
        for pos, gidx, cell in self._thumb_pos_map:
            try:
                is_sel = gidx in self.selected
                cell.configure(
                    highlightbackground=SEL_BD if is_sel else GRAY_LT)
                # 페이지 번호 라벨 색상
                for child in cell.winfo_children():
                    if isinstance(child, tk.Label) and child.cget("bg") == GRAY_LT:
                        child.configure(fg=GREEN_DK if is_sel else TEXT_TER)
            except tk.TclError:
                pass
        self._update_sel_label()

    # ═══════════════════════════════════════════════════════════
    # 페이지 이동 (앞/뒤, 특정 위치)
    # ═══════════════════════════════════════════════════════════
    def _move_forward(self):
        if not self.selected: return
        self._push_undo()
        order   = self.page_order[:]
        indices = sorted([order.index(p) for p in self.selected])
        if indices[0] == 0: return
        for i in indices:
            order[i-1], order[i] = order[i], order[i-1]
        self.page_order = order
        self._rebuild_thumbs()

    def _move_backward(self):
        if not self.selected: return
        self._push_undo()
        order   = self.page_order[:]
        indices = sorted([order.index(p) for p in self.selected], reverse=True)
        if indices[0] == len(order)-1: return
        for i in indices:
            order[i], order[i+1] = order[i+1], order[i]
        self.page_order = order
        self._rebuild_thumbs()

    def _move_to_pos_dialog(self):
        """선택 페이지를 특정 위치로 이동 — 방향 선택 가능한 커스텀 다이얼로그"""
        if not self.selected:
            messagebox.showwarning("알림", "이동할 페이지를 먼저 선택하세요."); return
        total    = len(self.page_order)
        sel_cnt  = len(self.selected)

        # ── 커스텀 다이얼로그 ──
        dlg = tk.Toplevel(self.root)
        dlg.title("특정 위치로 이동")
        dlg.configure(bg=CARD_BG)
        dlg.resizable(False, False)
        dlg.grab_set()
        x = self.root.winfo_x() + self.root.winfo_width()//2  - 200
        y = self.root.winfo_y() + self.root.winfo_height()//2 - 150
        dlg.geometry(f"400x300+{max(0,x)}+{max(0,y)}")

        tk.Label(dlg, text=f"선택된 {sel_cnt}페이지를 어디로 이동하시겠습니까?",
                 font=("Malgun Gothic",10), bg=CARD_BG, fg=TEXT_PRI,
                 pady=12).pack(fill="x", padx=16)
        tk.Frame(dlg, bg=BORDER, height=1).pack(fill="x", padx=16)

        mode_var = tk.StringVar(value="before")
        num_var  = tk.StringVar(value="1")
        result   = {"action": None}

        def make_radio(parent, text, val):
            rb = tk.Radiobutton(parent, text=text, variable=mode_var, value=val,
                                font=("Malgun Gothic",10), bg=CARD_BG, fg=TEXT_SEC,
                                activebackground=CARD_BG, cursor="hand2")
            rb.pack(anchor="w", padx=24, pady=3)
            return rb

        tk.Label(dlg, text="이동 방식", font=("Malgun Gothic",9),
                 bg=CARD_BG, fg=TEXT_TER).pack(anchor="w", padx=16, pady=(10,2))

        make_radio(dlg, "맨 앞으로",  "first")
        make_radio(dlg, "맨 뒤로",    "last")

        # 번호 입력 행 — 앞으로
        r_before = tk.Frame(dlg, bg=CARD_BG)
        r_before.pack(anchor="w", padx=24, pady=3)
        tk.Radiobutton(r_before, text="", variable=mode_var, value="before",
                       bg=CARD_BG, activebackground=CARD_BG).pack(side="left")
        tk.Label(r_before, text="페이지 번호",
                 font=("Malgun Gothic",10), bg=CARD_BG, fg=TEXT_SEC).pack(side="left")
        num_entry = tk.Entry(r_before, textvariable=num_var, width=6,
                             font=("Malgun Gothic",10), relief="solid", bd=1)
        num_entry.pack(side="left", padx=6)
        tk.Label(r_before, text=f"번 앞으로  (1~{total})",
                 font=("Malgun Gothic",10), bg=CARD_BG, fg=TEXT_SEC).pack(side="left")

        # 번호 입력 행 — 뒤로
        r_after = tk.Frame(dlg, bg=CARD_BG)
        r_after.pack(anchor="w", padx=24, pady=3)
        tk.Radiobutton(r_after, text="", variable=mode_var, value="after",
                       bg=CARD_BG, activebackground=CARD_BG).pack(side="left")
        tk.Label(r_after, text="페이지 번호",
                 font=("Malgun Gothic",10), bg=CARD_BG, fg=TEXT_SEC).pack(side="left")
        tk.Entry(r_after, textvariable=num_var, width=6,
                 font=("Malgun Gothic",10), relief="solid", bd=1).pack(side="left", padx=6)
        tk.Label(r_after, text=f"번 뒤로  (1~{total})",
                 font=("Malgun Gothic",10), bg=CARD_BG, fg=TEXT_SEC).pack(side="left")

        def _do_move():
            m = mode_var.get()
            dragged = set(self.selected)
            remain  = [p for p in self.page_order if p not in dragged]
            ordered = [p for p in self.page_order if p in dragged]

            if m == "first":
                new_order = ordered + remain
            elif m == "last":
                new_order = remain + ordered
            else:
                try:
                    num = int(num_var.get())
                    if num < 1 or num > total:
                        messagebox.showerror("오류", f"1~{total} 사이의 숫자를 입력하세요."); return
                except ValueError:
                    messagebox.showerror("오류", "숫자를 입력하세요."); return

                # 0-based 삽입 위치 계산
                if m == "before":
                    insert_pos = num - 1
                else:  # after
                    insert_pos = num  # num번 뒤 = num+1번 앞

                adj = sum(1 for p in dragged if self.page_order.index(p) < insert_pos)
                ri  = max(0, min(insert_pos - adj, len(remain)))
                new_order = remain[:]
                for i, p in enumerate(ordered):
                    new_order.insert(ri + i, p)

            self._push_undo()
            self.page_order = new_order
            result["action"] = True
            dlg.destroy()
            self._rebuild_thumbs()

        tk.Frame(dlg, bg=BORDER, height=1).pack(fill="x", padx=16, pady=10)
        btn_row = tk.Frame(dlg, bg=CARD_BG)
        btn_row.pack(padx=16, fill="x")
        tk.Button(btn_row, text="취소", font=("Malgun Gothic",10),
                  bg=CARD_BG, fg=TEXT_SEC, relief="solid", bd=1,
                  padx=16, pady=5, command=dlg.destroy
                  ).pack(side="right", padx=(6,0))
        tk.Button(btn_row, text="이동", font=("Malgun Gothic",10,"bold"),
                  bg=GREEN, fg="white", relief="flat",
                  padx=16, pady=5, command=_do_move
                  ).pack(side="right")

    # ═══════════════════════════════════════════════════════════
    # 삭제
    # ═══════════════════════════════════════════════════════════
    def _delete_selected(self):
        if not self.selected:
            messagebox.showwarning("알림", "삭제할 페이지를 선택하세요."); return
        if not messagebox.askyesno("삭제 확인",
            f"선택한 {len(self.selected)}페이지를 삭제하시겠습니까?\n"
            "Ctrl+Z로 되돌릴 수 있습니다."): return
        self._push_undo()
        self.page_order = [p for p in self.page_order if p not in self.selected]
        self.selected.clear()
        self._rebuild_thumbs()

    # ═══════════════════════════════════════════════════════════
    # 회전
    # ═══════════════════════════════════════════════════════════
    def _rotate_sel(self, deg):
        if not self.selected: return
        self._push_undo()
        for gidx in self.selected:
            self.rotations[gidx] = (self.rotations.get(gidx, 0) + deg) % 360
        self._rebuild_thumbs()

    # ═══════════════════════════════════════════════════════════
    # 추출
    # ═══════════════════════════════════════════════════════════
    def _extract_selected(self):
        if not self.selected:
            messagebox.showwarning("알림", "추출할 페이지를 선택하세요."); return
        path = filedialog.asksaveasfilename(title="추출 파일 저장",
            defaultextension=".pdf", filetypes=[("PDF","*.pdf")],
            initialdir=self.output_dir)
        if not path: return
        try:
            writer    = PdfWriter()
            open_docs = {}
            for gidx in self.page_order:
                if gidx not in self.selected: continue
                fp, li = self._resolve_page(gidx)
                if fp not in open_docs: open_docs[fp] = PdfReader(fp)
                page = open_docs[fp].pages[li]
                rot  = self.rotations.get(gidx, 0)
                if rot: page.rotate(rot)
                writer.add_page(page)
            with open(path,"wb") as f: writer.write(f)
            messagebox.showinfo("완료", f"추출 완료!\n{path}")
        except Exception as ex:
            messagebox.showerror("오류", str(ex))

    # ═══════════════════════════════════════════════════════════
    # 페이지 교체
    # ═══════════════════════════════════════════════════════════
    def _swap_with_page(self):
        """선택 페이지와 작업영역 내 다른 페이지 위치 교체"""
        if len(self.selected) != 1:
            messagebox.showwarning("알림", "교체할 페이지 1개만 선택하세요."); return
        total   = len(self.page_order)
        src_g   = list(self.selected)[0]
        src_pos = self.page_order.index(src_g) + 1
        val     = simpledialog.askinteger(
            "페이지 교체",
            f"현재 선택: {src_pos}페이지\n\n교체할 상대 페이지 번호를 입력하세요 (1~{total}):",
            minvalue=1, maxvalue=total)
        if val is None or val == src_pos: return
        self._push_undo()
        if src_g not in self.page_order:
            messagebox.showerror("오류", "선택한 페이지를 찾을 수 없습니다."); return
        si = self.page_order.index(src_g)
        ti = val - 1
        self.page_order[si], self.page_order[ti] = \
            self.page_order[ti], self.page_order[si]
        self._rebuild_thumbs()

    def _replace_with_external(self):
        """선택 페이지를 외부 PDF의 페이지(들)로 교체 — 전체/범위/직접지정"""
        if not self.selected:
            messagebox.showwarning("알림", "교체 기준 페이지를 선택하세요."); return
        if len(self.selected) != 1:
            messagebox.showwarning("알림", "교체 기준 페이지 1개만 선택하세요."); return

        ext_path = filedialog.askopenfilename(title="외부 PDF 선택",
            filetypes=[("PDF","*.pdf")])
        if not ext_path: return
        try:
            ext_reader = PdfReader(ext_path)
            ext_n      = len(ext_reader.pages)
        except Exception as ex:
            messagebox.showerror("오류", str(ex)); return

        # ── 커스텀 다이얼로그 ──
        dlg = tk.Toplevel(self.root)
        dlg.title("외부 PDF 페이지로 교체")
        dlg.configure(bg=CARD_BG)
        dlg.resizable(False, False)
        dlg.grab_set()
        x = self.root.winfo_x() + self.root.winfo_width()//2  - 210
        y = self.root.winfo_y() + self.root.winfo_height()//2 - 160
        dlg.geometry(f"420x340+{max(0,x)}+{max(0,y)}")

        tk.Label(dlg, text=f"외부 파일: {os.path.basename(ext_path)}  ({ext_n}페이지)",
                 font=("Malgun Gothic",10,"bold"), bg=CARD_BG, fg=TEXT_PRI,
                 pady=10).pack(fill="x", padx=16)
        tk.Label(dlg, text="삽입할 페이지를 선택하세요. 선택한 현재 페이지 위치에 삽입됩니다.",
                 font=("Malgun Gothic",9), bg=CARD_BG, fg=TEXT_TER,
                 wraplength=380, justify="left").pack(fill="x", padx=16)
        tk.Frame(dlg, bg=BORDER, height=1).pack(fill="x", padx=16, pady=6)

        mode_var = tk.StringVar(value="all")

        def make_radio(text, val):
            tk.Radiobutton(dlg, text=text, variable=mode_var, value=val,
                           font=("Malgun Gothic",10), bg=CARD_BG, fg=TEXT_SEC,
                           activebackground=CARD_BG, cursor="hand2"
                           ).pack(anchor="w", padx=24, pady=2)

        make_radio(f"전체 ({ext_n}페이지 전부 삽입)", "all")

        # 범위 지정
        r_range = tk.Frame(dlg, bg=CARD_BG)
        r_range.pack(anchor="w", padx=24, pady=2)
        tk.Radiobutton(r_range, text="", variable=mode_var, value="range",
                       bg=CARD_BG, activebackground=CARD_BG).pack(side="left")
        tk.Label(r_range, text="범위 지정:",
                 font=("Malgun Gothic",10), bg=CARD_BG, fg=TEXT_SEC).pack(side="left")
        range_s = tk.Entry(r_range, width=5, font=("Malgun Gothic",10),
                           relief="solid", bd=1)
        range_s.insert(0, "1")
        range_s.pack(side="left", padx=4)
        tk.Label(r_range, text="~", font=("Malgun Gothic",10),
                 bg=CARD_BG, fg=TEXT_SEC).pack(side="left")
        range_e = tk.Entry(r_range, width=5, font=("Malgun Gothic",10),
                           relief="solid", bd=1)
        range_e.insert(0, str(ext_n))
        range_e.pack(side="left", padx=4)
        tk.Label(r_range, text=f"페이지  (최대 {ext_n})",
                 font=("Malgun Gothic",9), bg=CARD_BG, fg=TEXT_TER).pack(side="left")

        # 직접 지정
        r_custom = tk.Frame(dlg, bg=CARD_BG)
        r_custom.pack(anchor="w", padx=24, pady=2)
        tk.Radiobutton(r_custom, text="", variable=mode_var, value="custom",
                       bg=CARD_BG, activebackground=CARD_BG).pack(side="left")
        tk.Label(r_custom, text="직접 지정:",
                 font=("Malgun Gothic",10), bg=CARD_BG, fg=TEXT_SEC).pack(side="left")
        custom_e = tk.Entry(r_custom, width=20, font=("Malgun Gothic",10),
                            relief="solid", bd=1)
        custom_e.insert(0, "1,3,5")
        custom_e.pack(side="left", padx=4)
        tk.Label(r_custom, text="쉼표로 구분",
                 font=("Malgun Gothic",9), bg=CARD_BG, fg=TEXT_TER).pack(side="left")

        def _do_replace():
            m = mode_var.get()
            try:
                if m == "all":
                    local_indices = list(range(ext_n))
                elif m == "range":
                    s = int(range_s.get()); e = int(range_e.get())
                    if s < 1 or e > ext_n or s > e:
                        messagebox.showerror("오류", f"올바른 범위를 입력하세요 (1~{ext_n})"); return
                    local_indices = list(range(s-1, e))
                elif m == "custom":
                    parts = [p.strip() for p in custom_e.get().split(",") if p.strip()]
                    local_indices = [int(p)-1 for p in parts]
                    if any(li < 0 or li >= ext_n for li in local_indices):
                        messagebox.showerror("오류", f"페이지 번호는 1~{ext_n} 사이여야 합니다."); return
            except ValueError:
                messagebox.showerror("오류", "올바른 숫자를 입력하세요."); return

            self._push_undo()
            src_g   = list(self.selected)[0]
            if src_g not in self.page_order:
                messagebox.showerror("오류", "선택한 페이지를 찾을 수 없습니다."); return
            src_idx = self.page_order.index(src_g)

            # 기존 선택 페이지 제거
            self.page_order.pop(src_idx)
            self.thumb_cache.pop(src_g, None)

            # 새 global_idx 들 할당 및 삽입
            new_gs = []
            next_g = (max(self._page_map.keys()) + 1) if self._page_map else 0
            for i, li in enumerate(local_indices):
                ng = next_g + i
                self._page_map[ng] = (ext_path, li)
                new_gs.append(ng)

            for i, ng in enumerate(new_gs):
                self.page_order.insert(src_idx + i, ng)

            self.selected = set(new_gs)
            dlg.destroy()

            # 썸네일 백그라운드 로드
            threading.Thread(
                target=lambda: self._load_multi_thumbs(new_gs, ext_path, local_indices),
                daemon=True).start()
            self._rebuild_thumbs()

        tk.Frame(dlg, bg=BORDER, height=1).pack(fill="x", padx=16, pady=10)
        br = tk.Frame(dlg, bg=CARD_BG)
        br.pack(padx=16, fill="x")
        tk.Button(br, text="취소", font=("Malgun Gothic",10),
                  bg=CARD_BG, fg=TEXT_SEC, relief="solid", bd=1,
                  padx=16, pady=5, command=dlg.destroy
                  ).pack(side="right", padx=(6,0))
        tk.Button(br, text="교체", font=("Malgun Gothic",10,"bold"),
                  bg=GREEN, fg="white", relief="flat",
                  padx=16, pady=5, command=_do_replace
                  ).pack(side="right")

    def _load_single_thumb(self, gidx, fpath, lidx):
        if not FITZ_AVAILABLE: return
        try:
            doc = fitz.open(fpath)
            if lidx >= len(doc): return
            pix = doc[lidx].get_pixmap(matrix=fitz.Matrix(0.6,0.6))
            img = Image.frombytes("RGB",[pix.width,pix.height],pix.samples)
            img.thumbnail((200,283), Image.LANCZOS)
            doc.close()
            self.thumb_cache[gidx] = img
            self.root.after(0, self._rebuild_thumbs)
        except Exception: pass

    def _load_multi_thumbs(self, gidxs, fpath, local_indices):
        """여러 페이지 썸네일 한꺼번에 로드"""
        if not FITZ_AVAILABLE: return
        try:
            doc = fitz.open(fpath)
            for gidx, li in zip(gidxs, local_indices):
                if li >= len(doc): continue
                pix = doc[li].get_pixmap(matrix=fitz.Matrix(0.6,0.6))
                img = Image.frombytes("RGB",[pix.width,pix.height],pix.samples)
                img.thumbnail((200,283), Image.LANCZOS)
                self.thumb_cache[gidx] = img
            doc.close()
            self.root.after(0, self._rebuild_thumbs)
        except Exception: pass

    # ═══════════════════════════════════════════════════════════
    # _resolve_page
    # ═══════════════════════════════════════════════════════════
    def _resolve_page(self, global_idx):
        if global_idx in self._page_map:
            return self._page_map[global_idx]
        return self.pdf_path, global_idx

    # ═══════════════════════════════════════════════════════════
    # 분할 모드
    # ═══════════════════════════════════════════════════════════
    def _toggle_split_mode(self):
        self.split_active = not self.split_active
        btn = self.tool_vars.get("split")
        if self.split_active:
            if btn: btn.configure(bg=GREEN_LT, fg=GREEN_DK)
            self.split_panel.pack(fill="x")
            self._set_split_mode(self.split_mode)
        else:
            if btn: btn.configure(bg=CARD_BG, fg=TEXT_SEC)
            self.split_panel.pack_forget()
            self.cut_points.clear()
            self.split_mode = "equal"
            for b in self.split_mode_btns.values():
                b.configure(bg=GRAY_LT, fg=TEXT_SEC)
            self._rebuild_thumbs()

    def _set_split_mode(self, mode):
        self.split_mode = mode
        for mid, b in self.split_mode_btns.items():
            if mid == mode: b.configure(bg=GREEN_LT, fg=GREEN_DK, relief="solid")
            else:           b.configure(bg=GRAY_LT,  fg=TEXT_SEC,  relief="solid")
        self.eq_frame.pack_forget()
        self.free_frame.pack_forget()
        self.click_frame.pack_forget()
        if mode == "equal":   self.eq_frame.pack(fill="x", padx=0)
        elif mode == "free":  self.free_frame.pack(fill="x", padx=0)
        else:                 self.click_frame.pack(fill="x", padx=8)
        self._rebuild_thumbs()

    def _validate_free_input(self, event=None):
        val = self.free_entry.get()
        if not val:
            self.free_err.configure(text=""); return True
        if not re.match(r'^[\d,\s]+$', val):
            self.free_err.configure(text="숫자와 쉼표만 입력 가능합니다."); return False
        parts = [p.strip() for p in val.split(",") if p.strip()]
        if any(int(p) <= 0 for p in parts if p.isdigit()):
            self.free_err.configure(text="1 이상의 숫자만 입력 가능합니다."); return False
        self.free_err.configure(text=""); return True

    def _parse_free_chunks(self):
        val   = self.free_entry.get()
        parts = [int(p.strip()) for p in val.split(",") if p.strip().isdigit()]
        total = len(self.page_order)
        s     = sum(parts)
        if s < total:   parts[-1] += (total - s)
        elif s > total:
            excess = s - total
            while excess > 0 and parts:
                r = min(parts[-1]-1, excess)
                parts[-1] -= r; excess -= r
                if parts[-1] <= 0: parts.pop()
        return parts

    # ═══════════════════════════════════════════════════════════
    # 저장
    # ═══════════════════════════════════════════════════════════
    def _save_pdf(self):
        if not self.pdf_path:
            messagebox.showwarning("알림","열린 PDF 파일이 없습니다."); return
        if self.split_active:
            self._do_split(); return
        choice = messagebox.askyesno("저장 방식 선택",
            "원본 파일을 덮어쓰시겠습니까?\n\n예 → 원본 덮어쓰기\n아니오 → 새 파일로 저장")
        if choice: self._write_pdf(self.pdf_path)
        else:      self._save_as_pdf()

    def _save_as_pdf(self):
        if not self.pdf_path:
            messagebox.showwarning("알림","열린 PDF 파일이 없습니다."); return
        if self.split_active:
            path = filedialog.asksaveasfilename(
                title="분할 저장 — 파일명 접두사 입력",
                defaultextension=".pdf", filetypes=[("PDF","*.pdf")],
                initialdir=self.output_dir,
                initialfile=os.path.splitext(os.path.basename(self.pdf_path))[0])
            if not path: return
            self._do_split(out_dir=os.path.dirname(path),
                           base=os.path.splitext(os.path.basename(path))[0])
        else:
            path = filedialog.asksaveasfilename(
                title="다른 이름으로 저장",
                defaultextension=".pdf", filetypes=[("PDF","*.pdf")],
                initialdir=self.output_dir,
                initialfile=os.path.basename(self.pdf_path))
            if path: self._write_pdf(path)

    def _write_pdf(self, out_path):
        try:
            writer    = PdfWriter()
            open_docs = {}
            for gidx in self.page_order:
                fp, li = self._resolve_page(gidx)
                if fp not in open_docs: open_docs[fp] = PdfReader(fp)
                if li >= len(open_docs[fp].pages):
                    raise IndexError(f"페이지 범위 초과 (global={gidx}, local={li})")
                page = open_docs[fp].pages[li]
                rot  = self.rotations.get(gidx, 0)
                if rot: page.rotate(rot)
                writer.add_page(page)
            with open(out_path,"wb") as f: writer.write(f)
            messagebox.showinfo("완료", f"저장 완료!\n{out_path}")
        except Exception as ex:
            messagebox.showerror("오류", str(ex))

    # ═══════════════════════════════════════════════════════════
    # 분할
    # ═══════════════════════════════════════════════════════════
    def _do_split(self, out_dir=None, base=None):
        if not self.pdf_path:
            messagebox.showwarning("알림","PDF 파일을 먼저 열어주세요."); return
        if not self.page_order: return

        mode   = self.split_mode
        chunks = []

        if mode == "equal":
            try:
                n = int(self.eq_entry.get())
                if n <= 0: raise ValueError
            except ValueError:
                messagebox.showerror("오류","1 이상의 숫자를 입력하세요."); return
            i = 0
            while i < len(self.page_order):
                chunks.append(self.page_order[i:i+n]); i += n

        elif mode == "free":
            if not self._validate_free_input():
                messagebox.showerror("오류","입력값을 확인하세요."); return
            sizes = self._parse_free_chunks()
            i     = 0
            for s in sizes:
                chunks.append(self.page_order[i:i+s]); i += s
            if i < len(self.page_order):
                chunks.append(self.page_order[i:])

        elif mode == "click":
            if not self.cut_points:
                messagebox.showwarning("알림","분할선을 먼저 지정하세요."); return
            total_len  = len(self.page_order)
            valid_cuts = sorted([c for c in self.cut_points if 0 < c < total_len])
            if not valid_cuts:
                messagebox.showwarning("알림","유효한 분할선이 없습니다."); return
            prev = 0
            for c in valid_cuts:
                chunk = self.page_order[prev:c]
                if chunk: chunks.append(chunk)
                prev = c
            last = self.page_order[prev:]
            if last: chunks.append(last)

        chunks = [c for c in chunks if c]  # 빈 구간 제거
        if not chunks:
            messagebox.showwarning("알림", "분할할 유효한 구간이 없습니다."); return
        self._save_chunks(chunks, out_dir=out_dir, base=base)

    def _save_chunks(self, chunks, out_dir=None, base=None):
        if not chunks:
            messagebox.showwarning("알림", "분할할 내용이 없습니다."); return
        if out_dir is None:
            out_dir = filedialog.askdirectory(title="분할 파일 저장 폴더 선택",
                                              initialdir=self.output_dir)
            if not out_dir: return
        if base is None:
            base = os.path.splitext(os.path.basename(self.pdf_path))[0]
        try:
            open_docs     = {}
            all_positions = {pg: pos for pos, pg in enumerate(self.page_order)}
            for i, chunk in enumerate(chunks):
                writer = PdfWriter()
                for gidx in chunk:
                    fp, li = self._resolve_page(gidx)
                    if fp not in open_docs: open_docs[fp] = PdfReader(fp)
                    rdr = open_docs[fp]
                    if li >= len(rdr.pages):
                        raise IndexError(
                            f"페이지 범위 초과: local={li}, 파일={os.path.basename(fp)}")
                    page = rdr.pages[li]
                    rot  = self.rotations.get(gidx, 0)
                    if rot: page.rotate(rot)
                    writer.add_page(page)
                s   = all_positions.get(chunk[0], 0) + 1
                e   = all_positions.get(chunk[-1], 0) + 1
                fn  = f"{base}_{str(s).zfill(4)}~{str(e).zfill(4)}.pdf"
                out = os.path.join(out_dir, fn)
                with open(out,"wb") as f: writer.write(f)
            messagebox.showinfo("완료", f"분할 완료!\n총 {len(chunks)}개 파일 → {out_dir}")
            self.cut_points.clear()
        except IndexError as ex:
            messagebox.showerror("인덱스 오류",
                f"페이지 인덱스가 범위를 벗어났습니다.\n\n{ex}\n\nPDF를 다시 불러온 후 시도해주세요.")
        except Exception as ex:
            messagebox.showerror("오류", str(ex))

    # ═══════════════════════════════════════════════════════════
    # 더블클릭 미리보기
    # ═══════════════════════════════════════════════════════════
    def _preview_page(self, gidx, pos):
        if not FITZ_AVAILABLE:
            messagebox.showinfo("알림","미리보기는 pymupdf 설치 시 사용 가능합니다."); return
        if gidx not in self._page_map:
            return  # 이미 삭제된 페이지

        win = tk.Toplevel(self.root)
        win.title(f"페이지 {pos+1} 미리보기")
        win.configure(bg=CARD_BG)
        win.resizable(True, True)

        rot     = self.rotations.get(gidx, 0)
        rot_txt = f"  (회전 {rot}°)" if rot else ""
        ibar    = tk.Frame(win, bg=CARD_BG,
                           highlightbackground=BORDER, highlightthickness=1)
        ibar.pack(fill="x")
        tk.Label(ibar, text=f"  페이지 {pos+1}{rot_txt}  —  더블클릭 미리보기",
                 font=("Malgun Gothic",9), bg=CARD_BG, fg=TEXT_TER, pady=5
                 ).pack(side="left")
        tk.Button(ibar, text="✕", font=("Malgun Gothic",10), bg=CARD_BG, fg=TEXT_TER,
                  relief="flat", bd=0, command=win.destroy).pack(side="right", padx=8)

        loading = tk.Label(win, text="⏳  로딩 중...",
                           font=("Malgun Gothic",13), bg=CARD_BG, fg=TEXT_TER)
        loading.pack(expand=True)

        # 임시 창
        x0 = self.root.winfo_x() + self.root.winfo_width()//2 - 200
        y0 = max(30, self.root.winfo_y())
        win.geometry(f"400x200+{max(0,x0)}+{y0}")

        def _load():
            try:
                fp, li = self._resolve_page(gidx)
                if not fp or not os.path.isfile(fp):
                    raise FileNotFoundError(f"파일 없음: {fp}")
                doc = fitz.open(fp)
                if li >= len(doc):
                    doc.close()
                    raise IndexError(f"페이지 범위 초과: {li}/{len(doc)}")

                pix0 = doc[li].get_pixmap(matrix=fitz.Matrix(1.0,1.0))
                ow, oh = pix0.width, pix0.height
                doc.close()

                rot2 = self.rotations.get(gidx, 0)
                dw, dh = (oh, ow) if rot2 in (90,270) else (ow, oh)

                sw    = self.root.winfo_screenwidth()
                sh    = self.root.winfo_screenheight()
                scale = min(sw*0.35/max(dw,1), sh*0.75/max(dh,1))
                ww    = int(dw*scale) + 20
                wh    = int(dh*scale) + 60

                rs   = max(0.3, min(scale*1.5, 3.0))
                doc2 = fitz.open(fp)
                pix2 = doc2[li].get_pixmap(matrix=fitz.Matrix(rs,rs))
                img  = Image.frombytes("RGB",[pix2.width,pix2.height],pix2.samples)
                doc2.close()
                if rot2: img = img.rotate(-rot2, expand=True)
                img.thumbnail((ww-16, wh-60), Image.LANCZOS)
                photo = ImageTk.PhotoImage(img)

                def _show():
                    if not win.winfo_exists(): return
                    loading.destroy()
                    # 창 위치: 항상 화면 상단 기준
                    wx = max(10, min(self.root.winfo_x() + self.root.winfo_width()//2 - ww//2,
                                    sw - ww - 10))
                    wy = max(30, min(30, sh - wh - 60))
                    win.geometry(f"{ww}x{wh}+{wx}+{wy}")
                    frame = tk.Frame(win, bg=GRAY_LT)
                    frame.pack(fill="both", expand=True)
                    cp = tk.Canvas(frame, bg=GRAY_LT, highlightthickness=0)
                    sv = ttk.Scrollbar(frame, orient="vertical",   command=cp.yview)
                    sh2= ttk.Scrollbar(frame, orient="horizontal", command=cp.xview)
                    cp.configure(yscrollcommand=sv.set, xscrollcommand=sh2.set)
                    sv.pack(side="right",  fill="y")
                    sh2.pack(side="bottom", fill="x")
                    cp.pack(fill="both", expand=True)
                    cp.create_image(8,8,anchor="nw",image=photo)
                    cp.configure(scrollregion=(0,0,photo.width()+16,photo.height()+16))
                    cp.image = photo
                    cp.bind("<MouseWheel>",
                            lambda e: cp.yview_scroll(int(-1*(e.delta/120)),"units"))

                win.after(0, _show)
            except Exception as ex:
                def _err():
                    if win.winfo_exists():
                        loading.configure(text=f"⚠  미리보기 실패\n\n{ex}",
                                          font=("Malgun Gothic",10), fg=RED)
                win.after(0, _err)

        threading.Thread(target=_load, daemon=True).start()

    # ═══════════════════════════════════════════════════════════
    # 도움말
    # ═══════════════════════════════════════════════════════════
    def _show_help(self):
        win = tk.Toplevel(self.root)
        win.title("도움말")
        win.configure(bg=CARD_BG)
        win.resizable(True, True)
        win.minsize(440, 500)
        win.grab_set()
        x = self.root.winfo_x() + self.root.winfo_width()//2  - 220
        y = self.root.winfo_y() + self.root.winfo_height()//2 - 280
        win.geometry(f"440x560+{max(0,x)}+{max(0,y)}")

        hdr = tk.Frame(win, bg=CARD_BG,
                       highlightbackground=BORDER, highlightthickness=1)
        hdr.pack(fill="x")
        tk.Label(hdr, text="도움말", font=("Malgun Gothic",12,"bold"),
                 bg=CARD_BG, fg=TEXT_PRI).pack(side="left", padx=12, pady=8)
        tk.Button(hdr, text="✕", font=("Malgun Gothic",11),
                  bg=CARD_BG, fg=TEXT_TER, relief="flat", bd=0,
                  command=win.destroy).pack(side="right", padx=8)

        tbar = tk.Frame(win, bg=CARD_BG,
                        highlightbackground=BORDER, highlightthickness=1)
        tbar.pack(fill="x")
        cf   = tk.Frame(win, bg=CARD_BG)
        cf.pack(fill="both", expand=True)
        pages_d = {}

        def sw(tid):
            for t, (b, p) in pages_d.items():
                if t == tid:
                    b.configure(fg=GREEN, font=("Malgun Gothic",10,"bold"))
                    p.pack(fill="both", expand=True)
                else:
                    b.configure(fg=TEXT_TER, font=("Malgun Gothic",10))
                    p.pack_forget()

        for tid, lbl in [("about","프로그램 정보"),("guide","기능 안내")]:
            btn  = tk.Label(tbar, text=lbl, font=("Malgun Gothic",10),
                            bg=CARD_BG, fg=TEXT_TER, padx=14, pady=6, cursor="hand2")
            btn.pack(side="left")
            page = tk.Frame(cf, bg=CARD_BG)
            pages_d[tid] = (btn, page)
            btn.bind("<Button-1>", lambda e, t=tid: sw(t))

        # 프로그램 정보
        _, ap = pages_d["about"]
        tk.Label(ap, text="✂", font=("Malgun Gothic",32),
                 bg=CARD_BG, fg=GREEN).pack(pady=(24,4))
        tk.Label(ap, text="PDF 편집기",
                 font=("Malgun Gothic",14,"bold"), bg=CARD_BG, fg=TEXT_PRI).pack()
        tk.Label(ap, text="v2.2",
                 font=("Malgun Gothic",10), bg=CARD_BG, fg=TEXT_TER).pack(pady=(2,8))
        tk.Label(ap, text="제가 회사에서 쓰려고 만든 프로그램입니다.",
                 font=("Malgun Gothic",10), bg=CARD_BG, fg=TEXT_SEC).pack(pady=(0,16))
        ifr = tk.Frame(ap, bg=CARD_BG)
        ifr.pack(padx=40, fill="x")
        tk.Frame(ifr, bg=BORDER, height=1).pack(fill="x", pady=(0,8))
        for lbl, val in [("제작자","양민수"),("버전","2.2"),
                         ("제작일","2026년 5월 19일"),("이메일","didandcl@naver.com")]:
            r = tk.Frame(ifr, bg=CARD_BG)
            r.pack(fill="x", pady=3)
            tk.Label(r, text=lbl, font=("Malgun Gothic",10),
                     bg=CARD_BG, fg=TEXT_TER, width=8, anchor="w").pack(side="left")
            tk.Label(r, text=val, font=("Malgun Gothic",10,"bold"),
                     bg=CARD_BG, fg=TEXT_SEC).pack(side="left")

        # 기능 안내
        _, gp = pages_d["guide"]
        sc = tk.Canvas(gp, bg=CARD_BG, highlightthickness=0)
        sb = ttk.Scrollbar(gp, orient="vertical", command=sc.yview)
        sc.configure(yscrollcommand=sb.set)
        sc.pack(side="left", fill="both", expand=True)
        sb.pack(side="right", fill="y")
        inner = tk.Frame(sc, bg=CARD_BG)
        sc.create_window((0,0), window=inner, anchor="nw")

        def _bmw(widget):
            widget.bind("<MouseWheel>",
                        lambda e: sc.yview_scroll(int(-1*(e.delta/120)),"units"))
            for child in widget.winfo_children():
                _bmw(child)

        inner.bind("<Configure>", lambda e: (
            sc.configure(scrollregion=sc.bbox("all")), _bmw(inner)))

        def gsec(t):
            tk.Label(inner, text=t, font=("Malgun Gothic",10,"bold"),
                     bg=CARD_BG, fg=TEXT_PRI, anchor="w"
                     ).pack(fill="x", padx=16, pady=(14,4))
            tk.Frame(inner, bg=BORDER, height=1).pack(fill="x", padx=16)

        def gitem(tag, desc):
            r = tk.Frame(inner, bg=CARD_BG)
            r.pack(fill="x", padx=16, pady=3)
            tk.Label(r, text=tag, font=("Malgun Gothic",9,"bold"),
                     bg=GREEN_LT, fg=GREEN_DK, padx=7, pady=2
                     ).pack(side="left", anchor="n")
            tk.Label(r, text=desc, font=("Malgun Gothic",9),
                     bg=CARD_BG, fg=TEXT_SEC, wraplength=310, justify="left", anchor="nw"
                     ).pack(side="left", padx=8, fill="x", expand=True)

        gsec("📋 썸네일 작업 영역")
        gitem("클릭",       "페이지를 선택합니다.")
        gitem("Shift+클릭", "범위를 한꺼번에 선택합니다.")
        gitem("Ctrl+클릭",  "여러 페이지를 개별 선택/해제합니다.")
        gitem("드래그",     "선택된 페이지를 원하는 위치로 이동합니다. 여러 페이지 선택 후 드래그하면 한 덩어리로 이동합니다.")
        gitem("더블클릭",   "해당 페이지를 크게 볼 수 있는 미리보기 창이 열립니다.")
        gitem("우클릭",     "회전·추출·위치이동·교체·삭제 메뉴가 표시됩니다.")
        gitem("Ctrl+휠",    "썸네일 크기를 조절합니다 (50~250px).")
        gitem("Ctrl+Z",     "직전 작업을 취소합니다. 최대 20단계.")
        gitem("선택 해제",  "툴바의 '선택 해제' 버튼으로 모든 선택을 해제합니다.")

        gsec("✂ 분할")
        gitem("분할 모드",  "좌측 '분할 모드' 버튼으로 활성/비활성 토글. 활성 상태에서 저장하면 분할 저장됩니다.")
        gitem("등분",       "입력한 숫자만큼 페이지씩 나눕니다. 예: 64페이지를 10으로 설정 → 10·10·10·10·10·10·4")
        gitem("자유입력",   "쉼표로 구간을 입력합니다. 예: 3,7,10,5,5 → 합계 불일치 시 나머지 자동 추가.")
        gitem("클릭지정",   "썸네일 사이의 ✂를 클릭해서 분할선을 직접 지정합니다.")

        gsec("📄 추출 / 🔄 회전 / 🗑 삭제")
        gitem("추출",   "선택 페이지만 별도 PDF로 저장합니다. 원본은 변경되지 않습니다.")
        gitem("회전",   "우클릭 → 90°·180°·270°. 여러 페이지 선택 시 모두 적용됩니다.")
        gitem("삭제",   "선택 페이지를 제거합니다. Ctrl+Z로 되돌릴 수 있습니다.")

        gsec("🔀 페이지 이동 / 교체")
        gitem("특정 위치로 이동", "우클릭 → '특정 위치로 이동' → 번호 입력. 선택된 페이지들이 해당 위치로 이동합니다.")
        gitem("작업영역 내 교체", "우클릭 → '작업영역 내 페이지와 교체' → 상대 페이지 번호 입력. 두 페이지 위치가 바뀝니다.")
        gitem("외부 파일로 교체", "우클릭 → '외부 PDF 페이지로 교체' → 파일 선택 → 페이지 번호 입력.")

        gsec("⚠ 파일 제한")
        gitem("용량",     f"{MAX_MB}MB 초과 시 경고 후 계속 여부 선택.")
        gitem("페이지 수", f"{MAX_PAGES}페이지 초과 시 동일하게 경고 후 선택.")

        tk.Frame(inner, bg=CARD_BG, height=16).pack()

        tk.Button(win, text="확인", font=("Malgun Gothic",10,"bold"),
                  bg=GREEN, fg="white", relief="flat", pady=7,
                  command=win.destroy).pack(fill="x", padx=16, pady=10)
        sw("about")

    # ═══════════════════════════════════════════════════════════
    # 오류 팝업
    # ═══════════════════════════════════════════════════════════
    def _error_popup(self, title, msg, filename=""):
        win = tk.Toplevel(self.root)
        win.title(title)
        win.configure(bg=CARD_BG)
        win.resizable(False, False)
        win.grab_set()
        x = self.root.winfo_x() + self.root.winfo_width()//2  - 175
        y = self.root.winfo_y() + self.root.winfo_height()//2 - 120
        win.geometry(f"350x240+{max(0,x)}+{max(0,y)}")
        tk.Label(win, text="⚠", font=("Malgun Gothic",30),
                 bg=CARD_BG, fg=RED).pack(pady=(20,4))
        tk.Label(win, text=title, font=("Malgun Gothic",12,"bold"),
                 bg=CARD_BG, fg=TEXT_PRI).pack()
        tk.Label(win, text=msg, font=("Malgun Gothic",10),
                 bg=CARD_BG, fg=TEXT_SEC).pack(pady=6)
        if filename:
            tk.Label(win, text=filename, font=("Consolas",9),
                     bg=RED_LT, fg=RED, padx=12, pady=4).pack()
        tk.Button(win, text="확인", font=("Malgun Gothic",11,"bold"),
                  bg=RED_LT, fg=RED, relief="solid", bd=1, pady=8,
                  command=win.destroy).pack(fill="x", padx=40, pady=18)


# ═══════════════════════════════════════════════════════════════
# 진입점
# ═══════════════════════════════════════════════════════════════
def main():
    if DND_AVAILABLE:
        root = TkinterDnD.Tk()
    else:
        root = tk.Tk()

    style = ttk.Style(root)
    style.theme_use("clam")
    style.configure("Horizontal.TProgressbar",
                    troughcolor=BORDER, background=GREEN, thickness=6)

    PDFEditorApp(root)
    root.mainloop()

if __name__ == "__main__":
    main()

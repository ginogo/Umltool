import tkinter as tk
from tkinter import ttk, filedialog, scrolledtext, messagebox, simpledialog
from PIL import Image, ImageTk
import subprocess
import os
import threading
from queue import Queue
from datetime import datetime
import shutil
import re
import json
from reportlab.pdfgen import canvas as pdf_canvas
from reportlab.lib.pagesizes import letter, A4, A3, landscape
import tempfile
import webbrowser
import sys
import logging

# 配置日志
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)


class UMLViewer:
    # PlantUML高质量设置模板（加强版：增加内外边距、最小宽度等）
    PLANTUML_QUALITY_HEADER = """
skinparam dpi 300
skinparam shadowing false
skinparam defaultFontName Microsoft YaHei
skinparam defaultFontSize 12
skinparam classAttributeIconSize 0
skinparam linetype ortho
skinparam pageExternalMargin 100   ' 强制外部边距
skinparam pageMargin 50            ' 内部边距
skinparam minClassWidth 200        ' 增加类的最小宽度，防止文字拥挤
skinparam componentStyle rectangle  ' 组件使用矩形样式，更清晰
"""

    def __init__(self, master):
        self.master = master
        self.master.title("UML工具 v2.8")

        # 配置路径
        self.jar_path = r"D:\Job\UML\plantuml-1.2025.2.jar"
        self.output_dir = r"D:\Job\UML\"
        self.version_dir = os.path.join(self.output_dir, "versions")
        self.temp_puml = os.path.join(self.output_dir, "temp.puml")
        self.temp_mmd = os.path.join(self.output_dir, "temp.mmd")
        self.temp_png = os.path.join(self.output_dir, "temp.png")
        self.temp_svg = os.path.join(self.output_dir, "temp.svg")
        self.temp_html = os.path.join(self.output_dir, "temp_mermaid.html")

        # 工具类型
        self.current_tool = "PlantUML"

        # Mermaid配置
        self.mermaid_theme = "neutral"
        self.mermaid_config = {
            "theme": self.mermaid_theme,
            "startOnLoad": True,
            "flowchart": {"useMaxWidth": False, "htmlLabels": True}
        }

        # 质量设置
        self.default_dpi = "300"

        # 高质量模式开关
        self.hq_mode = True

        # 原始图片尺寸（用于倍数计算）
        self.original_image_size = None

        # 检查mermaid-cli安装
        self.mermaid_cli_installed = self.check_mermaid_cli()

        # 语法高亮配置
        self.code_theme = {
            'comment': '#3C7A40', 'directive': '#FF7D00', 'preprocessor': '#FF5722',
            'keyword': '#1976D2', 'arrow': '#D32F2F', 'string': '#C62828',
            'number': '#6A1B9A', 'control': '#7B1FA2'
        }

        self.mermaid_code_theme = {
            'comment': '#3C7A40', 'keyword': '#1976D2', 'string': '#C62828',
            'number': '#6A1B9A', 'directive': '#FF7D00', 'function': '#7B1FA2', 'class': '#388E3C'
        }

        # 正则表达式模式
        self.plantuml_highlight_patterns = [
            (r'(?m)(#.*?$|//.*?$)', 'comment', self.code_theme['comment']),
            (r'(?i)@startuml|@enduml|@startmindmap|@endmindmap', 'directive', self.code_theme['directive']),
            (r'(?i)\b(title|header|footer|legend|newpage|skinparam)\b', 'directive', self.code_theme['directive']),
            (r'(?i)!(include|define|ifdef|endif|if|else)\b', 'preprocessor', self.code_theme['preprocessor']),
            (
            r'(?i)\b(class|interface|enum|abstract|extends|implements|as|package|namespace|node|component|state|object|actor|participant|usecase)\b',
            'keyword', self.code_theme['keyword']),
            (r'(-->|->>|->|\.\.>|--|<-|<--)', 'arrow', self.code_theme['arrow']),
            (r'"[^"]*"', 'string', self.code_theme['string']),
            (r'\b\d+\.?\d*\b', 'number', self.code_theme['number']),
            (r'(?i)\b(alt|else|opt|loop|par|break|critical|group|activate|deactivate|note|end|left|over|right)\b',
             'control', self.code_theme['control']),
        ]

        self.mermaid_highlight_patterns = [
            (r'(?m)(%%%.*?$)', 'comment', self.mermaid_code_theme['comment']),
            (
            r'(?i)\b(graph|flowchart|sequenceDiagram|classDiagram|stateDiagram|gantt|pie|gitGraph|erDiagram|journey|requirement)\b',
            'keyword', self.mermaid_code_theme['keyword']),
            (r'(?i)\b(LR|TD|TB|BT|RL|subgraph|end)\b', 'directive', self.mermaid_code_theme['directive']),
            (r'"[^"]*"|\'[^\']*\'', 'string', self.mermaid_code_theme['string']),
            (r'\b\d+\.?\d*\b', 'number', self.mermaid_code_theme['number']),
            (r'(?i)\b(click|style|link|call|participant|actor|note|rect|classDef|linkStyle)\b', 'function',
             self.mermaid_code_theme['function']),
            (r'(?i)class\s+\w+', 'class', self.mermaid_code_theme['class']),
            (r'(-->|--|==>|==|-.->|-\.|~~~|~~~>|--x|--o|->>|->)', 'arrow', self.code_theme['arrow']),
        ]

        # 图片相关属性
        self.current_image = None
        self.photo_image = None
        self.canvas_image = None
        self.zoom_scale = 1.0
        self.max_zoom = 5.0
        self.min_zoom = 0.1
        self.drag_data = {"x": 0, "y": 0, "dragging": False}

        # 首次显示标志
        self.first_display = True

        # 其他属性
        self.context_menu = None
        self.last_find_pos = None
        self.update_delay = 500
        self.after_id = None
        self.task_queue = Queue()

        # 初始化
        self.create_directories()
        self.create_widgets()
        self.setup_version_list()
        self.create_context_menu()
        self.bind_mousewheel_zoom()
        self.check_queue()
        self.generate_uml()

        logger.info("UML工具 v2.8 高质量版 初始化完成")

    def check_mermaid_cli(self):
        """检查mermaid-cli是否安装"""
        try:
            result = subprocess.run(
                ["mmdc", "--version"],
                capture_output=True, text=True,
                shell=True if sys.platform == "win32" else False,
                timeout=5,
                creationflags=subprocess.CREATE_NO_WINDOW if os.name == 'nt' else 0
            )
            if result.returncode == 0:
                logger.info(f"Mermaid-cli已安装: {result.stdout.strip()}")
                return True
        except Exception as e:
            logger.info(f"Mermaid-cli未安装: {e}")
        return False

    def create_directories(self):
        os.makedirs(self.version_dir, exist_ok=True)
        os.makedirs(self.output_dir, exist_ok=True)

    def create_widgets(self):
        """构建界面"""
        main_container = ttk.Frame(self.master)
        main_container.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

        # 顶部工具栏
        toolbar_frame = ttk.Frame(main_container)
        toolbar_frame.pack(fill=tk.X, pady=(0, 5))

        ttk.Label(toolbar_frame, text="绘图工具:", font=('微软雅黑', 10)).pack(side=tk.LEFT, padx=(5, 2))
        self.tool_var = tk.StringVar(value="PlantUML")
        self.tool_combobox = ttk.Combobox(toolbar_frame, textvariable=self.tool_var,
                                          values=["PlantUML", "Mermaid"], state="readonly", width=12, font=('微软雅黑', 10))
        self.tool_combobox.pack(side=tk.LEFT, padx=2)
        self.tool_combobox.bind("<<ComboboxSelected>>", self.on_tool_changed)

        # 高质量模式开关
        self.hq_var = tk.BooleanVar(value=True)
        self.hq_check = ttk.Checkbutton(toolbar_frame, text="高质量模式", variable=self.hq_var,
                                        command=self.on_hq_changed)
        self.hq_check.pack(side=tk.LEFT, padx=(10, 2))

        ttk.Label(toolbar_frame, text="Mermaid主题:", font=('微软雅黑', 10)).pack(side=tk.LEFT, padx=(10, 2))
        self.theme_var = tk.StringVar(value="neutral")
        self.theme_combobox = ttk.Combobox(toolbar_frame, textvariable=self.theme_var,
                                           values=["default", "dark", "forest", "neutral"], state="readonly", width=10,
                                           font=('微软雅黑', 10))
        self.theme_combobox.pack(side=tk.LEFT, padx=2)
        self.theme_combobox.bind("<<ComboboxSelected>>", self.on_theme_changed)

        ttk.Label(toolbar_frame, text="DPI:", font=('微软雅黑', 10)).pack(side=tk.LEFT, padx=(10, 2))
        self.dpi_var = tk.StringVar(value=self.default_dpi)
        ttk.Combobox(toolbar_frame, textvariable=self.dpi_var,
                     values=["72", "150", "300", "600", "1200"], state="readonly", width=6, font=('微软雅黑', 10)).pack(
            side=tk.LEFT, padx=2)
        self.dpi_var.trace_add("write", self.on_dpi_changed)

        self.status_label = ttk.Label(toolbar_frame, text=f"状态: PlantUML | DPI: {self.default_dpi} | 高质量模式",
                                      font=('微软雅黑', 9))
        self.status_label.pack(side=tk.LEFT, padx=(20, 2))

        ttk.Button(toolbar_frame, text="PlantUML示例", command=lambda: self.load_template("plantuml")).pack(side=tk.LEFT,
                                                                                                          padx=(20, 2))
        ttk.Button(toolbar_frame, text="Mermaid示例", command=lambda: self.load_template("mermaid")).pack(side=tk.LEFT,
                                                                                                        padx=2)
        ttk.Button(toolbar_frame, text="浏览器预览", command=self.open_in_browser).pack(side=tk.LEFT, padx=(20, 2))

        # 主面板
        main_pan = ttk.PanedWindow(main_container, orient=tk.HORIZONTAL)
        main_pan.pack(fill=tk.BOTH, expand=True)

        # 左侧面板
        left_pan = ttk.PanedWindow(main_pan, orient=tk.VERTICAL)

        # 代码编辑区
        editor_frame = ttk.Frame(left_pan, height=600)
        self.code_editor = scrolledtext.ScrolledText(editor_frame, wrap=tk.WORD, font=('Consolas', 11), undo=True,
                                                     maxundo=100)
        self.code_editor.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        self.setup_highlight_tags()
        self.code_editor.bind("<KeyRelease>", self.schedule_operations)
        self.code_editor.bind("<FocusIn>", self.highlight)
        self.code_editor.bind("<Return>", self.auto_indent)

        btn_frame = ttk.Frame(editor_frame)
        ttk.Button(btn_frame, text="生成图形", command=self.start_async_generation).pack(side=tk.LEFT, padx=5)
        ttk.Button(btn_frame, text="保存图形", command=self.save_image_dialog).pack(side=tk.LEFT, padx=5)
        btn_frame.pack(pady=5)

        left_pan.add(editor_frame, weight=3)

        # 版本管理区
        version_frame = ttk.Frame(left_pan, height=200)
        save_frame = ttk.Frame(version_frame)
        self.version_comment = ttk.Entry(save_frame, width=20)
        self.version_comment.pack(side=tk.LEFT, padx=2)
        ttk.Button(save_frame, text="保存版本", command=self.save_version).pack(side=tk.LEFT, padx=2)
        save_frame.pack(pady=2)

        list_frame = ttk.Frame(version_frame)
        self.version_list = tk.Listbox(list_frame, height=4)
        scrollbar = ttk.Scrollbar(list_frame, orient="vertical", command=self.version_list.yview)
        self.version_list.configure(yscrollcommand=scrollbar.set)
        self.version_list.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        list_frame.pack(fill=tk.BOTH, expand=True, padx=5)
        self.version_list.bind("<<ListboxSelect>>", self.load_version)

        left_pan.add(version_frame, weight=1)
        main_pan.add(left_pan)

        # 右侧面板
        right_frame = ttk.Frame(main_pan)

        zoom_frame = ttk.Frame(right_frame)
        ttk.Label(zoom_frame, text="预览缩放:").pack(side=tk.LEFT)
        self.zoom_slider = ttk.Scale(zoom_frame, from_=self.min_zoom, to=self.max_zoom, value=1.0,
                                     command=self.on_zoom_changed)
        self.zoom_slider.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=5)
        self.zoom_entry = ttk.Entry(zoom_frame, width=5)
        self.zoom_entry.pack(side=tk.LEFT, padx=2)
        self.zoom_entry.insert(0, "适应")
        self.zoom_entry.bind("<Return>", self.zoom_entry_changed)
        self.zoom_entry.bind("<FocusOut>", self.zoom_entry_changed)
        ttk.Button(zoom_frame, text="重置", command=self.reset_zoom).pack(side=tk.LEFT)
        ttk.Button(zoom_frame, text="适应窗口", command=self.fit_to_window).pack(side=tk.LEFT, padx=5)
        zoom_frame.pack(fill=tk.X, padx=5, pady=2)

        self.canvas = tk.Canvas(right_frame, bg='white')
        self.canvas.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

        v_scroll = ttk.Scrollbar(right_frame, orient="vertical", command=self.canvas.yview)
        h_scroll = ttk.Scrollbar(right_frame, orient="horizontal", command=self.canvas.xview)
        self.canvas.configure(yscrollcommand=v_scroll.set, xscrollcommand=h_scroll.set)
        v_scroll.pack(side=tk.RIGHT, fill=tk.Y)
        h_scroll.pack(side=tk.BOTTOM, fill=tk.X)

        self.canvas.bind("<ButtonPress-1>", self.start_drag)
        self.canvas.bind("<B1-Motion>", self.on_drag)
        self.canvas.bind("<ButtonRelease-1>", self.end_drag)
        self.canvas.bind("<Configure>", self.on_canvas_resize)

        main_pan.add(right_frame)

    def on_canvas_resize(self, event=None):
        """画布大小变化时自动适应"""
        if self.first_display and self.current_image:
            self.master.after(100, self.fit_to_window)

    def on_hq_changed(self):
        """高质量模式切换"""
        self.hq_mode = self.hq_var.get()
        self.update_status_label()
        self.start_async_generation()

    def update_status_label(self):
        """更新状态标签"""
        current_dpi = self.dpi_var.get()
        hq_status = "高质量模式" if self.hq_mode else "普通模式"

        # 显示原始图片尺寸
        size_info = ""
        if self.original_image_size:
            size_info = f" | 原始: {self.original_image_size[0]}x{self.original_image_size[1]}"

        if self.current_tool == "Mermaid":
            self.status_label.config(
                text=f"状态: {'Mermaid-cli' if self.mermaid_cli_installed else '浏览器预览'} | DPI: {current_dpi} | {hq_status}{size_info}",
                foreground="green" if self.mermaid_cli_installed else "orange"
            )
        else:
            self.status_label.config(
                text=f"状态: PlantUML | DPI: {current_dpi} | {hq_status}{size_info}",
                foreground="blue"
            )

    def on_dpi_changed(self, *args):
        self.update_status_label()

    def setup_highlight_tags(self):
        for tag in self.code_editor.tag_names():
            if tag not in ["sel", "highlight"]:
                self.code_editor.tag_delete(tag)
        patterns = self.plantuml_highlight_patterns if self.current_tool == "PlantUML" else self.mermaid_highlight_patterns
        for pattern, tag_name, color in patterns:
            self.code_editor.tag_configure(tag_name, foreground=color)

    def on_tool_changed(self, event=None):
        self.current_tool = self.tool_var.get()
        self.setup_highlight_tags()
        self.highlight()
        self.update_status_label()
        self.canvas.delete("all")
        self.first_display = True
        self.original_image_size = None
        self.start_async_generation()

    def on_theme_changed(self, event=None):
        self.mermaid_theme = self.theme_var.get()
        self.mermaid_config["theme"] = self.mermaid_theme
        if self.current_tool == "Mermaid":
            self.start_async_generation()

    def load_template(self, template_type):
        if template_type == "plantuml":
            template = """@startuml
title PlantUML示例 - 类图
class Animal {
    - name: String
    + Animal(name: String)
    + getName(): String
    + makeSound(): void
}
class Dog {
    - breed: String
    + Dog(name: String, breed: String)
    + getBreed(): String
    + makeSound(): void
}
class Cat {
    - color: String
    + Cat(name: String, color: String)
    + getColor(): String
    + makeSound(): void
}
Animal <|-- Dog
Animal <|-- Cat
@enduml"""
        else:
            template = """%% Mermaid示例 - 流程图
graph TD
    A[开始] --> B{条件判断}
    B -->|条件1| C[处理1]
    B -->|条件2| D[处理2]
    C --> E[合并]
    D --> E
    E --> F[结束]
    style A fill:#e1f5fe,stroke:#039be5,stroke-width:2px
    style B fill:#fff3e0,stroke:#ff9800,stroke-width:2px"""
        self.code_editor.delete("1.0", tk.END)
        self.code_editor.insert("1.0", template)
        self.highlight()
        self.first_display = True
        self.original_image_size = None
        self.start_async_generation()

    def open_in_browser(self):
        if self.current_tool == "Mermaid" and os.path.exists(self.temp_html):
            webbrowser.open(f"file://{os.path.abspath(self.temp_html)}")
        elif self.current_tool == "PlantUML":
            if os.path.exists(self.temp_svg):
                webbrowser.open(f"file://{os.path.abspath(self.temp_svg)}")
            elif os.path.exists(self.temp_png):
                webbrowser.open(f"file://{os.path.abspath(self.temp_png)}")
        else:
            messagebox.showinfo("提示", "请先生成图形")

    def create_context_menu(self):
        self.context_menu = tk.Menu(self.code_editor, tearoff=0)
        self.context_menu.add_command(label="查找", command=self.show_find_dialog)
        self.context_menu.add_command(label="替换", command=self.show_replace_dialog)
        self.code_editor.bind("<Button-3>", self.show_context_menu)

    def show_context_menu(self, event):
        self.context_menu.tk_popup(event.x_root, event.y_root)

    def show_find_dialog(self):
        search_str = simpledialog.askstring("查找", "输入查找内容:")
        if search_str:
            self.find_text(search_str)

    def show_replace_dialog(self):
        dialog = tk.Toplevel(self.master)
        dialog.title("替换")
        ttk.Label(dialog, text="查找内容:").grid(row=0, column=0, padx=5, pady=2)
        find_entry = ttk.Entry(dialog)
        find_entry.grid(row=0, column=1, padx=5, pady=2)
        ttk.Label(dialog, text="替换为:").grid(row=1, column=0, padx=5, pady=2)
        replace_entry = ttk.Entry(dialog)
        replace_entry.grid(row=1, column=1, padx=5, pady=2)

        def do_replace():
            self.replace_text(find_entry.get(), replace_entry.get())
            dialog.destroy()

        ttk.Button(dialog, text="替换", command=do_replace).grid(row=2, column=1, padx=5, pady=5)

    def find_text(self, search_str, start_pos="1.0"):
        self.code_editor.tag_remove("highlight", "1.0", tk.END)
        if not search_str:
            return
        start_idx = self.code_editor.search(search_str, start_pos, stopindex=tk.END, nocase=False, regexp=False)
        if start_idx:
            end_idx = f"{start_idx}+{len(search_str)}c"
            self.code_editor.tag_add("highlight", start_idx, end_idx)
            self.code_editor.tag_config("highlight", background="#FFD700")
            self.code_editor.see(start_idx)
            self.last_find_pos = end_idx
        else:
            messagebox.showinfo("查找", "已到达文档末尾")
            self.last_find_pos = None

    def replace_text(self, find_str, replace_str):
        if not find_str:
            return
        content = self.code_editor.get("1.0", tk.END)
        count = content.count(find_str)
        new_content = content.replace(find_str, replace_str)
        if new_content != content:
            self.code_editor.delete("1.0", tk.END)
            self.code_editor.insert("1.0", new_content)
            messagebox.showinfo("替换", f"共替换了{count}处")
        else:
            messagebox.showinfo("替换", "未找到匹配内容")

    def bind_mousewheel_zoom(self):
        self.canvas.bind("<Control-MouseWheel>", self.on_ctrl_scroll)
        self.canvas.bind("<Control-Button-4>", self.on_ctrl_scroll)
        self.canvas.bind("<Control-Button-5>", self.on_ctrl_scroll)

    def on_ctrl_scroll(self, event):
        delta = 0
        if event.num == 4 or (hasattr(event, 'delta') and event.delta > 0):
            delta = 0.1
        elif event.num == 5 or (hasattr(event, 'delta') and event.delta < 0):
            delta = -0.1
        new_scale = max(self.min_zoom, min(self.zoom_scale + delta, self.max_zoom))
        if new_scale != self.zoom_scale:
            self.zoom_scale = round(new_scale, 2)
            self.zoom_slider.set(self.zoom_scale)
            self.zoom_entry.delete(0, tk.END)
            self.zoom_entry.insert(0, f"{int(self.zoom_scale * 100)}%")
            self.update_preview()
        return "break"

    def schedule_operations(self, event=None):
        if self.after_id:
            self.master.after_cancel(self.after_id)
        self.after_id = self.master.after(self.update_delay, lambda: [self.start_async_generation(), self.highlight()])

    def auto_indent(self, event):
        line = self.code_editor.get("insert linestart", "insert lineend")
        match = re.match(r'^(\s+)', line)
        whitespace = match.group(1) if match else ""
        self.code_editor.insert("insert", f"\n{whitespace}")
        return "break"

    def highlight(self, event=None):
        patterns = self.plantuml_highlight_patterns if self.current_tool == "PlantUML" else self.mermaid_highlight_patterns
        for pattern, tag, _ in patterns:
            self.code_editor.tag_remove(tag, "1.0", "end")
        text = self.code_editor.get("1.0", "end-1c")
        for pattern, tag, _ in patterns:
            try:
                for match in re.finditer(pattern, text, re.MULTILINE):
                    start, end = match.start(), match.end()
                    start_line = text.count('\n', 0, start) + 1
                    last_nl = text.rfind('\n', 0, start)
                    start_col = start - (last_nl + 1) if last_nl != -1 else start
                    end_line = text.count('\n', 0, end) + 1
                    last_nl_end = text.rfind('\n', 0, end)
                    end_col = end - (last_nl_end + 1) if last_nl_end != -1 else end
                    self.code_editor.tag_add(tag, f"{start_line}.{start_col}", f"{end_line}.{end_col}")
            except:
                continue

    def setup_version_list(self):
        self.version_list.delete(0, tk.END)
        files = sorted([f for f in os.listdir(self.version_dir) if f.endswith((".puml", ".mmd"))],
                       key=lambda x: os.path.getmtime(os.path.join(self.version_dir, x)), reverse=True)
        for f in files:
            self.version_list.insert(tk.END, f)

    def save_version(self):
        comment = self.version_comment.get().strip()
        timestamp = datetime.now().strftime("%Y%m%d-%H%M%S")
        ext = ".puml" if self.current_tool == "PlantUML" else ".mmd"
        filename = f"{timestamp}_{comment[:20]}{ext}" if comment else f"{timestamp}{ext}"
        save_path = os.path.join(self.version_dir, filename)
        try:
            with open(save_path, "w", encoding="utf-8") as f:
                f.write(self.code_editor.get("1.0", tk.END))
            self.setup_version_list()
            self.version_comment.delete(0, tk.END)
            messagebox.showinfo("保存成功", f"版本已保存为: {filename}")
        except Exception as e:
            messagebox.showerror("保存失败", f"无法保存版本：{str(e)}")

    def load_version(self, event):
        """加载版本"""
        selection = self.version_list.curselection()
        if not selection:
            return
        filename = self.version_list.get(selection[0])
        filepath = os.path.join(self.version_dir, filename)
        try:
            with open(filepath, "r", encoding="utf-8") as f:
                content = f.read()

            if filename.endswith(".puml"):
                self.current_tool = "PlantUML"
                self.tool_var.set("PlantUML")
            elif filename.endswith(".mmd"):
                self.current_tool = "Mermaid"
                self.tool_var.set("Mermaid")

            self.setup_highlight_tags()
            self.code_editor.delete("1.0", tk.END)
            self.code_editor.insert("1.0", content)
            self.first_display = True
            self.original_image_size = None
            self.update_status_label()
            self.highlight()
            self.start_async_generation()
            logger.info(f"已加载版本: {filename}")
        except Exception as e:
            logger.error(f"加载版本失败: {str(e)}")
            messagebox.showerror("加载失败", f"无法加载版本：{str(e)}")

    def generate_uml(self):
        self.highlight()
        self.start_async_generation()

    def start_async_generation(self):
        if threading.active_count() < 5:
            threading.Thread(target=self.async_generation, daemon=True).start()

    def async_generation(self):
        try:
            current_dpi = int(self.dpi_var.get())
            if self.current_tool == "PlantUML":
                self.generate_plantuml_preview(current_dpi)
            else:
                self.generate_mermaid_preview(current_dpi)
        except Exception as e:
            self.task_queue.put(lambda: self.show_error(f"生成错误：{str(e)}"))

    def add_quality_settings(self, uml_code):
        """在PlantUML代码中自动添加高质量设置"""
        if not self.hq_mode:
            return uml_code

        # 始终插入我们的设置（即使有skinparam，也追加在后面，保证我们的生效）
        match = re.search(r'@startuml\s*\n?', uml_code, re.IGNORECASE)
        if match:
            insert_pos = match.end()
            return uml_code[:insert_pos] + self.PLANTUML_QUALITY_HEADER + uml_code[insert_pos:]
        else:
            return self.PLANTUML_QUALITY_HEADER + uml_code

    def generate_plantuml_preview(self, dpi):
        """生成PlantUML预览 - 采用动态边框和尺寸限制"""
        try:
            uml_code = self.code_editor.get("1.0", tk.END)
            if not uml_code.strip():
                self.task_queue.put(lambda: self.canvas.delete("all"))
                return

            uml_code_hq = self.add_quality_settings(uml_code)

            if "@startuml" not in uml_code_hq:
                uml_code_hq = "@startuml\n" + uml_code_hq
            if "@enduml" not in uml_code_hq:
                uml_code_hq = uml_code_hq + "\n@enduml\n"

            with open(self.temp_puml, "w", encoding="utf-8") as f:
                f.write(uml_code_hq)

            # 预览缩放倍数（高质量模式为2倍，普通模式为1倍）
            preview_scale = 2.0 if self.hq_mode else 1.0
            # 边框基数（3000像素）乘以缩放倍数，确保边框足够
            border_size = int(3000 * preview_scale) if self.hq_mode else 0

            # 构建PNG生成命令
            cmd_png = [
                "java", "-jar", self.jar_path,
                "-DPLANTUML_LIMIT_SIZE=65536",  # 允许更大画布
                "-charset", "UTF-8",
            ]
            if self.hq_mode and border_size > 0:
                cmd_png.extend(["-border", str(border_size)])
            cmd_png.extend(["-scale", str(preview_scale)])  # 缩放后加上边框，确保边框也按比例
            cmd_png.extend(["-o", self.output_dir, self.temp_puml])

            # SVG命令（同样添加边框和尺寸限制）
            cmd_svg = [
                "java", "-jar", self.jar_path,
                "-DPLANTUML_LIMIT_SIZE=65536",
                "-charset", "UTF-8",
                "-tsvg",
            ]
            if self.hq_mode and border_size > 0:
                cmd_svg.extend(["-border", str(border_size)])
            cmd_svg.extend(["-o", self.output_dir, self.temp_puml])

            logger.info(f"PlantUML预览PNG命令: {' '.join(cmd_png)}")
            logger.info(f"PlantUML预览SVG命令: {' '.join(cmd_svg)}")

            result_png = subprocess.run(cmd_png, check=True, capture_output=True, text=True,
                                        shell=True if sys.platform == "win32" else False,
                                        creationflags=subprocess.CREATE_NO_WINDOW if os.name == 'nt' else 0)

            subprocess.run(cmd_svg, capture_output=True, text=True,
                           shell=True if sys.platform == "win32" else False,
                           creationflags=subprocess.CREATE_NO_WINDOW if os.name == 'nt' else 0)

            base_name = os.path.splitext(os.path.basename(self.temp_puml))[0]
            source_png = os.path.join(self.output_dir, f"{base_name}.png")
            source_svg = os.path.join(self.output_dir, f"{base_name}.svg")

            if os.path.exists(source_png) and source_png != self.temp_png:
                shutil.copyfile(source_png, self.temp_png)

            if os.path.exists(source_svg) and source_svg != self.temp_svg:
                shutil.copyfile(source_svg, self.temp_svg)

            if os.path.exists(self.temp_png):
                img = Image.open(self.temp_png)
                # 保存图片（不改变DPI，预览用）
                img.save(self.temp_png)
                self.original_image_size = img.size
                self.task_queue.put(lambda: self.update_status_label())
                logger.info(f"预览图生成成功: {self.temp_png}, 原始尺寸: {img.size}")
                self.task_queue.put(lambda: self.show_preview(self.temp_png))
            else:
                self.task_queue.put(lambda: self.show_error("PNG文件未生成"))

        except subprocess.CalledProcessError as e:
            self.task_queue.put(lambda: self.show_error(f"PlantUML错误：{e.stderr[:200] if e.stderr else str(e)}"))
        except Exception as e:
            self.task_queue.put(lambda: self.show_error(f"系统错误：{str(e)}"))

    def generate_mermaid_preview(self, dpi):
        """生成Mermaid预览（保持不变）"""
        try:
            mmd_code = self.code_editor.get("1.0", tk.END)
            if not mmd_code.strip():
                self.task_queue.put(lambda: self.canvas.delete("all"))
                return

            with open(self.temp_mmd, "w", encoding="utf-8") as f:
                f.write(mmd_code)

            html_content = f"""<!DOCTYPE html>
<html><head><script src="https://cdn.jsdelivr.net/npm/mermaid/dist/mermaid.min.js"></script>
<script>mermaid.initialize({json.dumps(self.mermaid_config)});</script>
<style>body {{ margin: 0; padding: 20px; background: white; }} .mermaid {{ width: 100%; text-align: center; }}</style>
</head><body><div class="mermaid">{mmd_code}</div></body></html>"""
            with open(self.temp_html, "w", encoding="utf-8") as f:
                f.write(html_content)

            if self.mermaid_cli_installed:
                width, height, scale = 1920, 1080, 2.0
                cmd = ["mmdc", "-i", self.temp_mmd, "-o", self.temp_png, "-t", self.mermaid_theme,
                       "-w", str(width), "-H", str(height), "-b", "white", "-s", str(scale)]
                result = subprocess.run(cmd, capture_output=True, text=True,
                                        shell=True if sys.platform == "win32" else False, timeout=30,
                                        creationflags=subprocess.CREATE_NO_WINDOW if os.name == 'nt' else 0)
                if result.returncode == 0 and os.path.exists(self.temp_png):
                    img = Image.open(self.temp_png)
                    img.save(self.temp_png)  # 不设置DPI
                    self.original_image_size = img.size
                    self.task_queue.put(lambda: self.update_status_label())
                    self.task_queue.put(lambda: self.show_preview(self.temp_png))
                else:
                    self.task_queue.put(lambda: self.show_mermaid_message())
            else:
                self.task_queue.put(lambda: self.show_mermaid_message())
        except Exception as e:
            self.task_queue.put(lambda: self.show_error(f"Mermaid错误：{str(e)}"))

    def show_mermaid_message(self, error_msg=None):
        self.canvas.delete("all")
        message = "Mermaid图形预览\n\n"
        message += "✅ PNG预览可用\n" if self.mermaid_cli_installed else "⚠️ 未检测到mermaid-cli\n"
        if error_msg:
            message += f"\n错误: {error_msg}\n"
        message += "\n点击'浏览器预览'按钮查看完整效果"
        self.canvas.create_text(200, 100, text=message, fill="blue", font=('微软雅黑', 12), anchor=tk.NW, width=600)

    def check_queue(self):
        while not self.task_queue.empty():
            task = self.task_queue.get()
            try:
                task()
            except Exception as e:
                logger.error(f"队列任务执行错误: {str(e)}")
        self.master.after(100, self.check_queue)

    def zoom_entry_changed(self, event=None):
        try:
            value = self.zoom_entry.get().strip("%")
            if value.lower() == "适应":
                self.fit_to_window()
                return
            new_scale = float(value) / 100
            if self.min_zoom <= new_scale <= self.max_zoom:
                self.zoom_scale = round(new_scale, 2)
                self.zoom_slider.set(self.zoom_scale)
                self.zoom_entry.delete(0, tk.END)
                self.zoom_entry.insert(0, f"{int(self.zoom_scale * 100)}%")
                self.update_preview()
        except:
            self.zoom_entry.delete(0, tk.END)
            self.zoom_entry.insert(0, f"{int(self.zoom_scale * 100)}%")

    def on_zoom_changed(self, value):
        self.zoom_scale = round(float(value), 2)
        self.zoom_entry.delete(0, tk.END)
        self.zoom_entry.insert(0, f"{int(self.zoom_scale * 100)}%")
        self.update_preview()

    def reset_zoom(self):
        self.zoom_scale = 1.0
        self.zoom_slider.set(1.0)
        self.zoom_entry.delete(0, tk.END)
        self.zoom_entry.insert(0, "100%")
        self.update_preview()

    def fit_to_window(self):
        """适应窗口大小"""
        if self.current_image:
            canvas_width = self.canvas.winfo_width()
            canvas_height = self.canvas.winfo_height()

            if canvas_width > 1 and canvas_height > 1:
                scale = min(canvas_width / self.current_image.width,
                            canvas_height / self.current_image.height) * 0.95
                self.zoom_scale = max(self.min_zoom, min(round(scale, 2), self.max_zoom))
                self.zoom_slider.set(self.zoom_scale)
                self.zoom_entry.delete(0, tk.END)
                self.zoom_entry.insert(0, f"{int(self.zoom_scale * 100)}%")
                self.update_preview()
                self.first_display = False

    def update_preview(self):
        if self.current_image:
            try:
                new_size = (int(self.current_image.width * self.zoom_scale),
                            int(self.current_image.height * self.zoom_scale))
                resized = self.current_image.resize(new_size, Image.Resampling.LANCZOS)
                self.photo_image = ImageTk.PhotoImage(resized)
                self.canvas.delete("all")
                self.canvas_image = self.canvas.create_image(0, 0, anchor=tk.NW, image=self.photo_image)
                self.canvas.configure(scrollregion=(0, 0, new_size[0], new_size[1]))
            except Exception as e:
                self.show_error(f"缩放失败：{str(e)}")

    def show_preview(self, image_path):
        try:
            if os.path.exists(image_path):
                if self.current_image:
                    self.current_image.close()
                self.current_image = Image.open(image_path)

                if self.first_display:
                    self.zoom_entry.delete(0, tk.END)
                    self.zoom_entry.insert(0, "适应")
                    self.master.after(100, self.fit_to_window)
                else:
                    self.zoom_entry.delete(0, tk.END)
                    self.zoom_entry.insert(0, f"{int(self.zoom_scale * 100)}%")
                    self.update_preview()

                logger.info(f"显示图片: {image_path}, 尺寸: {self.current_image.size}")
        except Exception as e:
            self.show_error(f"图片加载失败：{str(e)}")

    def start_drag(self, event):
        self.canvas.scan_mark(event.x, event.y)
        self.drag_data["dragging"] = True
        self.canvas.config(cursor="hand1")

    def on_drag(self, event):
        if self.drag_data["dragging"]:
            self.canvas.scan_dragto(event.x, event.y, gain=1)

    def end_drag(self, event):
        self.drag_data["dragging"] = False
        self.canvas.config(cursor="")

    def add_margin_to_image(self, img, vertical_margin_mm, horizontal_margin_mm, dpi):
        """
        为图片添加边距
        :param img: PIL Image对象
        :param vertical_margin_mm: 上下边距（毫米）
        :param horizontal_margin_mm: 左右边距（毫米）
        :param dpi: DPI值
        :return: 带边距的新图片
        """
        # 将mm转换为像素 (1 inch = 25.4 mm)
        vertical_margin_px = int(vertical_margin_mm * dpi / 25.4)
        horizontal_margin_px = int(horizontal_margin_mm * dpi / 25.4)

        # 计算新图片尺寸
        new_width = img.width + 2 * horizontal_margin_px
        new_height = img.height + 2 * vertical_margin_px

        logger.info(
            f"添加边距: 上下{vertical_margin_mm}mm={vertical_margin_px}px, 左右{horizontal_margin_mm}mm={horizontal_margin_px}px")
        logger.info(f"原图尺寸: {img.width}x{img.height}, 新图尺寸: {new_width}x{new_height}")

        # 创建白色背景的新图片
        new_img = Image.new('RGB', (new_width, new_height), 'white')

        # 将原图粘贴到中心位置
        x_offset = horizontal_margin_px
        y_offset = vertical_margin_px
        new_img.paste(img, (x_offset, y_offset))

        return new_img

    def save_image_dialog(self):
        """保存图形对话框 - 倍数设置（保持不变）"""
        dialog = tk.Toplevel(self.master)
        dialog.title("保存选项 - 高质量版")
        dialog.grab_set()
        dialog.transient(self.master)

        current_dpi = self.dpi_var.get()

        # 使用Frame作为主容器
        main_frame = ttk.Frame(dialog, padding="10")
        main_frame.pack(fill=tk.BOTH, expand=True)

        # 高品质设置框架
        quality_frame = ttk.LabelFrame(main_frame, text="输出尺寸设置（基于原图形倍数）", padding="10")
        quality_frame.pack(fill=tk.X, pady=(0, 10))

        entries = {}
        row = 0

        # 显示原始尺寸
        if self.original_image_size:
            orig_w, orig_h = self.original_image_size
            orig_label = ttk.Label(quality_frame,
                                   text=f"📐 原始图形尺寸: {orig_w} x {orig_h} px",
                                   foreground="blue", font=('微软雅黑', 10, 'bold'))
            orig_label.grid(row=row, column=0, columnspan=4, pady=5, sticky="w")
            row += 1

        # 高质量模式提示
        if self.hq_mode:
            hq_label = ttk.Label(quality_frame, text="✅ 高质量模式已开启", foreground="green")
            hq_label.grid(row=row, column=0, columnspan=4, pady=5, sticky="w")
            row += 1

        # 宽度倍数
        ttk.Label(quality_frame, text="宽度倍数:").grid(row=row, column=0, padx=5, pady=5, sticky="w")
        width_scale_var = tk.StringVar(value="3.0")
        width_scale_entry = ttk.Entry(quality_frame, textvariable=width_scale_var, width=10)
        width_scale_entry.grid(row=row, column=1, padx=5, pady=5, sticky="w")
        ttk.Label(quality_frame, text="倍").grid(row=row, column=2, padx=5, pady=5, sticky="w")
        row += 1

        # 高度倍数
        ttk.Label(quality_frame, text="高度倍数:").grid(row=row, column=0, padx=5, pady=5, sticky="w")
        height_scale_var = tk.StringVar(value="3.0")
        height_scale_entry = ttk.Entry(quality_frame, textvariable=height_scale_var, width=10)
        height_scale_entry.grid(row=row, column=1, padx=5, pady=5, sticky="w")
        ttk.Label(quality_frame, text="倍").grid(row=row, column=2, padx=5, pady=5, sticky="w")
        row += 1

        # 锁定宽高比
        lock_ratio_var = tk.BooleanVar(value=True)
        lock_check = ttk.Checkbutton(quality_frame, text="锁定宽高比例", variable=lock_ratio_var)
        lock_check.grid(row=row, column=0, columnspan=4, pady=5, sticky="w")
        row += 1

        # 计算后的尺寸显示
        calc_label = ttk.Label(quality_frame, text="输出尺寸: -- x -- px", foreground="green", font=('微软雅黑', 10))
        calc_label.grid(row=row, column=0, columnspan=4, pady=5, sticky="w")
        row += 1

        # 绑定倍数变化事件
        def update_calculated_size(*args):
            try:
                w_scale = float(width_scale_var.get())
                h_scale = float(height_scale_var.get())
                if self.original_image_size:
                    orig_w, orig_h = self.original_image_size
                    calc_w = int(orig_w * w_scale)
                    calc_h = int(orig_h * h_scale)
                    calc_label.config(text=f"输出尺寸: {calc_w} x {calc_h} px")
            except:
                calc_label.config(text="输出尺寸: -- x -- px")

        width_scale_var.trace_add("write", update_calculated_size)
        height_scale_var.trace_add("write", update_calculated_size)

        if self.original_image_size:
            update_calculated_size()

        # DPI设置
        ttk.Label(quality_frame, text="输出DPI:").grid(row=row, column=0, padx=5, pady=5, sticky="w")
        entries["dpi"] = ttk.Entry(quality_frame, width=10)
        entries["dpi"].insert(0, current_dpi)
        entries["dpi"].grid(row=row, column=1, padx=5, pady=5, sticky="w")
        row += 1

        # 预设倍数按钮
        preset_frame = ttk.Frame(quality_frame)
        ttk.Button(preset_frame, text="1x", width=5,
                   command=lambda: [width_scale_var.set("1.0"), height_scale_var.set("1.0")]).pack(side=tk.LEFT, padx=2)
        ttk.Button(preset_frame, text="2x", width=5,
                   command=lambda: [width_scale_var.set("2.0"), height_scale_var.set("2.0")]).pack(side=tk.LEFT, padx=2)
        ttk.Button(preset_frame, text="3x", width=5,
                   command=lambda: [width_scale_var.set("3.0"), height_scale_var.set("3.0")]).pack(side=tk.LEFT, padx=2)
        ttk.Button(preset_frame, text="4x", width=5,
                   command=lambda: [width_scale_var.set("4.0"), height_scale_var.set("4.0")]).pack(side=tk.LEFT, padx=2)
        ttk.Button(preset_frame, text="6x", width=5,
                   command=lambda: [width_scale_var.set("6.0"), height_scale_var.set("6.0")]).pack(side=tk.LEFT, padx=2)
        ttk.Button(preset_frame, text="8x", width=5,
                   command=lambda: [width_scale_var.set("8.0"), height_scale_var.set("8.0")]).pack(side=tk.LEFT, padx=2)
        preset_frame.grid(row=row, column=0, columnspan=4, pady=10)
        row += 1

        # 格式设置
        format_frame = ttk.LabelFrame(main_frame, text="格式设置", padding="10")
        format_frame.pack(fill=tk.X, pady=(0, 10))

        ttk.Label(format_frame, text="文件格式:").grid(row=0, column=0, padx=5, pady=5, sticky="w")
        format_var = tk.StringVar(value="png")

        if self.current_tool == "PlantUML":
            format_values = ["png", "svg", "pdf"]
        else:
            format_values = ["png", "pdf", "html"]

        format_combo = ttk.Combobox(format_frame, textvariable=format_var, values=format_values, state="readonly",
                                    width=12)
        format_combo.grid(row=0, column=1, padx=5, pady=5, sticky="w")

        format_note_label = ttk.Label(format_frame, text="", foreground="blue")
        format_note_label.grid(row=0, column=2, padx=5, pady=5, sticky="w")

        def on_format_changed(event=None):
            if format_var.get() == "svg":
                format_note_label.config(text="SVG为矢量格式，无损缩放")
            elif format_var.get() == "png":
                format_note_label.config(text="PNG为位图格式")
            elif format_var.get() == "pdf":
                format_note_label.config(text="PDF适合打印")
            else:
                format_note_label.config(text="")

        format_combo.bind("<<ComboboxSelected>>", on_format_changed)
        on_format_changed()

        # PDF页面大小
        ttk.Label(format_frame, text="PDF页面大小:").grid(row=1, column=0, padx=5, pady=5, sticky="w")
        pdf_size_var = tk.StringVar(value="A4")
        ttk.Combobox(format_frame, textvariable=pdf_size_var, values=["A4", "A3", "Letter", "A4-横向", "A3-横向"],
                     state="readonly", width=12).grid(row=1, column=1, padx=5, pady=5, sticky="w")

        # 边距设置
        ttk.Label(format_frame, text="上下边距(mm):").grid(row=2, column=0, padx=5, pady=5, sticky="w")
        entries["vertical"] = ttk.Entry(format_frame, width=10)
        entries["vertical"].insert(0, "10")
        entries["vertical"].grid(row=2, column=1, padx=5, pady=5, sticky="w")

        ttk.Label(format_frame, text="左右边距(mm):").grid(row=3, column=0, padx=5, pady=5, sticky="w")
        entries["horizontal"] = ttk.Entry(format_frame, width=10)
        entries["horizontal"].insert(0, "10")
        entries["horizontal"].grid(row=3, column=1, padx=5, pady=5, sticky="w")

        # 边距说明
        margin_note = ttk.Label(format_frame, text="* 边距应用于PNG和PDF格式", foreground="gray")
        margin_note.grid(row=4, column=0, columnspan=3, pady=5, sticky="w")

        # 按钮框架
        btn_frame = ttk.Frame(main_frame)
        btn_frame.pack(fill=tk.X, pady=10)

        ttk.Button(btn_frame, text="开始保存", command=lambda: self.on_save_clicked_v2(
            width_scale_var.get(), height_scale_var.get(), lock_ratio_var.get(),
            entries["vertical"].get(), entries["horizontal"].get(),
            entries["dpi"].get(), pdf_size_var.get(), format_var.get(), dialog)).pack(side=tk.LEFT, padx=5)
        ttk.Button(btn_frame, text="取消", command=dialog.destroy).pack(side=tk.LEFT, padx=5)

        # 设置窗口大小
        dialog.update_idletasks()
        window_width = 500
        window_height = 700
        x = (dialog.winfo_screenwidth() - window_width) // 2
        y = (dialog.winfo_screenheight() - window_height) // 2
        dialog.geometry(f"{window_width}x{window_height}+{x}+{y}")
        dialog.minsize(window_width, window_height)

    def on_save_clicked_v2(self, width_scale, height_scale, lock_ratio, vertical, horizontal, dpi, pdf_size, fmt,
                           dialog):
        """保存按钮点击（保持不变）"""
        try:
            error_msg = []

            try:
                w_scale = float(width_scale)
                if not (0.1 <= w_scale <= 20.0):
                    error_msg.append("宽度倍数必须在0.1到20.0之间")
            except ValueError:
                error_msg.append("宽度倍数必须是数字")

            try:
                h_scale = float(height_scale)
                if not (0.1 <= h_scale <= 20.0):
                    error_msg.append("高度倍数必须在0.1到20.0之间")
            except ValueError:
                error_msg.append("高度倍数必须是数字")

            try:
                dpi_value = int(dpi.strip())
                if not (72 <= dpi_value <= 1200):
                    error_msg.append("DPI必须在72-1200之间")
            except ValueError:
                error_msg.append("DPI必须是整数")

            try:
                vertical_margin = int(vertical.strip()) if vertical.strip() else 10
                if vertical_margin < 0:
                    error_msg.append("上下边距不能为负数")
            except ValueError:
                error_msg.append("上下边距必须是整数")
                vertical_margin = 10

            try:
                horizontal_margin = int(horizontal.strip()) if horizontal.strip() else 10
                if horizontal_margin < 0:
                    error_msg.append("左右边距不能为负数")
            except ValueError:
                error_msg.append("左右边距必须是整数")
                horizontal_margin = 10

            if error_msg:
                messagebox.showerror("参数错误", "\n".join(error_msg))
                return

            dialog.destroy()
            self.perform_save_v2(w_scale, h_scale, lock_ratio,
                                 vertical_margin, horizontal_margin,
                                 dpi_value, pdf_size, fmt)
        except Exception as e:
            messagebox.showerror("保存失败", f"参数处理错误：{str(e)}")

    def perform_save_v2(self, width_scale, height_scale, lock_ratio, vertical_margin, horizontal_margin, dpi, pdf_size,
                        file_format):
        """执行保存"""
        try:
            if self.current_tool == "PlantUML":
                self.save_plantuml_v2(width_scale, height_scale, lock_ratio, vertical_margin, horizontal_margin, dpi,
                                      pdf_size, file_format)
            else:
                self.save_mermaid_v2(width_scale, height_scale, vertical_margin, horizontal_margin, dpi, pdf_size,
                                     file_format)
        except Exception as e:
            messagebox.showerror("保存失败", f"保存过程中发生错误：{str(e)}")

    def save_plantuml_v2(self, width_scale, height_scale, lock_ratio, vertical_margin, horizontal_margin, dpi, pdf_size,
                         file_format):
        """保存PlantUML - 采用动态边框和尺寸限制"""
        try:
            uml_code = self.code_editor.get("1.0", tk.END)

            if not self.original_image_size:
                messagebox.showwarning("警告", "请先生成预览图形")
                return

            orig_w, orig_h = self.original_image_size

            if lock_ratio:
                scale = max(width_scale, height_scale)
                output_w = int(orig_w * scale)
                output_h = int(orig_h * scale)
            else:
                scale = max(width_scale, height_scale)  # 用于边框计算
                output_w = int(orig_w * width_scale)
                output_h = int(orig_h * height_scale)

            logger.info(f"PlantUML保存: 原始尺寸={orig_w}x{orig_h}, 输出尺寸={output_w}x{output_h}, DPI={dpi}, 格式={file_format}")
            logger.info(f"边距设置: 上下={vertical_margin}mm, 左右={horizontal_margin}mm")

            uml_code_hq = self.add_quality_settings(uml_code)

            if "@startuml" not in uml_code_hq:
                uml_code_hq = "@startuml\n" + uml_code_hq
            if "@enduml" not in uml_code_hq:
                uml_code_hq = uml_code_hq + "\n@enduml\n"

            with open(self.temp_puml, "w", encoding="utf-8") as f:
                f.write(uml_code_hq)

            file_path = filedialog.asksaveasfilename(
                defaultextension=f".{file_format.lower()}",
                filetypes=[(f"{file_format.upper()} Files", f"*.{file_format.lower()}"), ("All Files", "*.*")]
            )

            if not file_path:
                return

            # 动态计算边框大小（基数3000，乘以缩放倍数）
            border_size = int(3000 * scale) if self.hq_mode else 0

            if file_format.lower() == "svg":
                cmd_svg = [
                    "java", "-jar", self.jar_path,
                    "-DPLANTUML_LIMIT_SIZE=65536",
                    "-charset", "UTF-8",
                    "-tsvg",
                ]
                if self.hq_mode and border_size > 0:
                    cmd_svg.extend(["-border", str(border_size)])
                cmd_svg.extend(["-o", os.path.dirname(file_path), self.temp_puml])

                subprocess.run(cmd_svg, check=True, capture_output=True, text=True,
                               shell=True if sys.platform == "win32" else False,
                               creationflags=subprocess.CREATE_NO_WINDOW if os.name == 'nt' else 0)

                base_name = os.path.splitext(os.path.basename(self.temp_puml))[0]
                source_svg = os.path.join(os.path.dirname(file_path), f"{base_name}.svg")

                if os.path.exists(source_svg):
                    with open(source_svg, 'r', encoding='utf-8') as f:
                        svg_content = f.read()

                    with open(file_path, 'w', encoding='utf-8') as f:
                        f.write(svg_content)

                    if source_svg != file_path:
                        os.remove(source_svg)

                    messagebox.showinfo("保存成功", f"SVG矢量文件已保存到：\n{file_path}\n\n✅ 矢量格式，无损缩放！")
                else:
                    raise Exception("SVG文件未生成")

            elif file_format.lower() in ["png", "pdf"]:
                cmd_scale = [
                    "java", "-jar", self.jar_path,
                    "-DPLANTUML_LIMIT_SIZE=65536",
                    "-charset", "UTF-8",
                ]
                if self.hq_mode and border_size > 0:
                    cmd_scale.extend(["-border", str(border_size)])
                cmd_scale.extend(["-scale", str(scale)])
                cmd_scale.extend(["-o", self.output_dir, self.temp_puml])

                subprocess.run(cmd_scale, check=True, capture_output=True, text=True,
                               shell=True if sys.platform == "win32" else False,
                               creationflags=subprocess.CREATE_NO_WINDOW if os.name == 'nt' else 0)

                base_name = os.path.splitext(os.path.basename(self.temp_puml))[0]
                scaled_png = os.path.join(self.output_dir, f"{base_name}.png")

                if os.path.exists(scaled_png):
                    img = Image.open(scaled_png)

                    actual_w, actual_h = img.size
                    if lock_ratio and (actual_w != output_w or actual_h != output_h):
                        final_scale = min(output_w / actual_w, output_h / actual_h)
                        new_w = int(actual_w * final_scale)
                        new_h = int(actual_h * final_scale)
                        img = img.resize((new_w, new_h), Image.Resampling.LANCZOS)

                        if new_w != output_w or new_h != output_h:
                            final_img = Image.new('RGB', (output_w, output_h), 'white')
                            x_offset = (output_w - new_w) // 2
                            y_offset = (output_h - new_h) // 2
                            final_img.paste(img, (x_offset, y_offset))
                            img = final_img

                    # 为用户手动设置的边距
                    if vertical_margin > 0 or horizontal_margin > 0:
                        img = self.add_margin_to_image(img, vertical_margin, horizontal_margin, dpi)

                    if file_format.lower() == "png":
                        img.save(file_path, dpi=(dpi, dpi), quality=95)
                        messagebox.showinfo("保存成功",
                                            f"高质量PNG已保存到：\n{file_path}\n\n原始尺寸: {orig_w}x{orig_h}\n输出尺寸: {img.width}x{img.height}\n放大倍数: {scale:.1f}x\n边距: 上下{vertical_margin}mm, 左右{horizontal_margin}mm\nDPI: {dpi}")
                    else:
                        temp_png = os.path.join(self.output_dir, "temp_pdf.png")
                        img.save(temp_png, dpi=(dpi, dpi), quality=95)
                        self.convert_png_to_pdf(temp_png, file_path, vertical_margin, horizontal_margin, dpi, pdf_size)
                        if os.path.exists(temp_png):
                            os.remove(temp_png)
                        messagebox.showinfo("保存成功",
                                            f"PDF已保存到：\n{file_path}\n\n原始尺寸: {orig_w}x{orig_h}\n放大倍数: {scale:.1f}x\n边距: 上下{vertical_margin}mm, 左右{horizontal_margin}mm")
                else:
                    raise Exception("PNG文件未生成")

        except subprocess.CalledProcessError as e:
            messagebox.showerror("生成错误", f"PlantUML生成失败：\n{e.stderr[:500] if e.stderr else str(e)}")
        except Exception as e:
            logger.error(f"保存失败: {str(e)}")
            messagebox.showerror("保存失败", f"保存过程中发生错误：{str(e)}")

    def save_mermaid_v2(self, width_scale, height_scale, vertical_margin, horizontal_margin, dpi, pdf_size,
                        file_format):
        """保存Mermaid（保持不变）"""
        try:
            mmd_code = self.code_editor.get("1.0", tk.END)

            if not self.original_image_size:
                messagebox.showwarning("警告", "请先生成预览图形")
                return

            orig_w, orig_h = self.original_image_size
            output_w = int(orig_w * width_scale)
            output_h = int(orig_h * height_scale)

            logger.info(f"Mermaid保存: 原始尺寸={orig_w}x{orig_h}, 输出尺寸={output_w}x{output_h}, DPI={dpi}")
            logger.info(f"边距设置: 上下={vertical_margin}mm, 左右={horizontal_margin}mm")

            with open(self.temp_mmd, "w", encoding="utf-8") as f:
                f.write(mmd_code)

            file_path = filedialog.asksaveasfilename(
                defaultextension=f".{file_format.lower()}",
                filetypes=[(f"{file_format.upper()} Files", f"*.{file_format.lower()}"), ("All Files", "*.*")]
            )

            if not file_path:
                return

            if file_format.lower() == "html":
                html_content = f"""<!DOCTYPE html>
<html><head><script src="https://cdn.jsdelivr.net/npm/mermaid/dist/mermaid.min.js"></script>
<script>mermaid.initialize({json.dumps(self.mermaid_config)});</script>
<style>body {{ margin: 0; padding: {vertical_margin}px {horizontal_margin}px; background: white; }}
.mermaid {{ width: {output_w}px; height: {output_h}px; text-align: center; }}</style>
</head><body><div class="mermaid">{mmd_code}</div></body></html>"""
                with open(file_path, "w", encoding="utf-8") as f:
                    f.write(html_content)
                messagebox.showinfo("保存成功", f"HTML文件已保存到：\n{file_path}")

            elif self.mermaid_cli_installed:
                temp_png = os.path.join(tempfile.gettempdir(), "mermaid_hq_output.png")
                scale = max(width_scale, height_scale)
                cmd = ["mmdc", "-i", self.temp_mmd, "-o", temp_png, "-t", self.mermaid_theme,
                       "-w", str(output_w), "-H", str(output_h), "-b", "white", "-s", str(scale)]
                logger.info(f"Mermaid命令: {' '.join(cmd)}")

                subprocess.run(cmd, check=True, shell=True if sys.platform == "win32" else False,
                               timeout=120, creationflags=subprocess.CREATE_NO_WINDOW if os.name == 'nt' else 0)

                if os.path.exists(temp_png):
                    img = Image.open(temp_png)

                    # 为PNG添加边距
                    if vertical_margin > 0 or horizontal_margin > 0:
                        img = self.add_margin_to_image(img, vertical_margin, horizontal_margin, dpi)

                    img.save(temp_png, dpi=(dpi, dpi), quality=95)

                    if file_format.lower() == "pdf":
                        self.convert_png_to_pdf(temp_png, file_path, vertical_margin, horizontal_margin, dpi, pdf_size)
                    else:
                        shutil.copyfile(temp_png, file_path)
                    os.remove(temp_png)

                    messagebox.showinfo("保存成功",
                                        f"高质量文件已保存到：\n{file_path}\n\n原始尺寸: {orig_w}x{orig_h}\n输出尺寸: {img.width}x{img.height}\n放大倍数: {scale:.1f}x\n边距: 上下{vertical_margin}mm, 左右{horizontal_margin}mm\nDPI: {dpi}")
            else:
                messagebox.showwarning("功能限制", "需要安装mermaid-cli才能生成PNG/PDF")
                return

        except Exception as e:
            messagebox.showerror("保存失败", f"保存过程中发生错误：{str(e)}")

    def convert_png_to_pdf(self, png_path, pdf_path, vertical_margin, horizontal_margin, dpi, page_size):
        """PNG转PDF（保持不变）"""
        try:
            img = Image.open(png_path)

            if page_size == "A4":
                page_width, page_height = A4
            elif page_size == "A3":
                page_width, page_height = A3
            elif page_size == "A4-横向":
                page_width, page_height = landscape(A4)
            elif page_size == "A3-横向":
                page_width, page_height = landscape(A3)
            else:
                page_width, page_height = letter

            margin_v_pts = vertical_margin * 2.83465
            margin_h_pts = horizontal_margin * 2.83465
            available_width = page_width - 2 * margin_h_pts
            available_height = page_height - 2 * margin_v_pts

            logger.info(f"PDF转换: 页面大小={page_size}, 边距=上下{vertical_margin}mm/左右{horizontal_margin}mm")
            logger.info(f"可用区域: {available_width:.1f}x{available_height:.1f}pt")

            img_width_pts = img.width * 72 / dpi
            img_height_pts = img.height * 72 / dpi
            scale = min(available_width / img_width_pts, available_height / img_height_pts, 1.0)

            scaled_width = img_width_pts * scale
            scaled_height = img_height_pts * scale
            x = margin_h_pts + (available_width - scaled_width) / 2
            y = margin_v_pts + (available_height - scaled_height) / 2

            c = pdf_canvas.Canvas(pdf_path, pagesize=(page_width, page_height))
            c.drawImage(png_path, x, y, width=scaled_width, height=scaled_height, mask='auto')
            c.setTitle("UML Diagram")
            c.setAuthor("UML Tool v2.8 高质量版")
            c.save()
            logger.info(f"PDF已生成: {pdf_path}")
        except Exception as e:
            messagebox.showerror("转换失败", f"PDF生成失败：{str(e)}")

    def show_error(self, message):
        self.canvas.delete("all")
        self.canvas.create_text(100, 50, text=message, fill="red", font=('微软雅黑', 12), anchor=tk.NW)


if __name__ == "__main__":
    root = tk.Tk()
    root.geometry("2400x1600")
    app = UMLViewer(root)
    root.mainloop()
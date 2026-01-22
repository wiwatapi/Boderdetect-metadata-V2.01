import os
import tkinter as tk
from tkinter import filedialog, messagebox
import ttkbootstrap as ttk
from ttkbootstrap.constants import *
import threading
import queue
import time
import math
import shutil
import datetime
import re
from math import gcd

# Image processing libraries
import cv2
import numpy as np
from PIL import Image, ImageTk
import imagehash
import multiprocessing
from concurrent.futures import ProcessPoolExecutor

# ===== Duplicate Detection Settings =====
# Based on PhotoSweep's proven approach
HASH_SIZE = 16  # Larger = more accurate (PhotoSweep uses 16)
SIMILARITY_THRESHOLD = 5  # Hamming distance threshold (lower = stricter, was 10)

# ===== Helper function for Unicode path support =====
def imread_unicode(filepath, flags=cv2.IMREAD_COLOR):
    """
    Read image with Unicode path support (Thai, Japanese, Chinese, etc.)
    cv2.imread doesn't support Unicode paths on Windows, so we use numpy.fromfile
    """
    try:
        # Read file as bytes using numpy (supports Unicode paths)
        img_array = np.fromfile(filepath, dtype=np.uint8)
        # Decode the bytes as an image
        img = cv2.imdecode(img_array, flags)
        return img
    except Exception as e:
        print(f"Error reading {filepath}: {e}")
        return None

class AdobeStockChecker:
    def __init__(self, root):
        self.root = root
        
        # ตั้งชื่อหน้าต่างพร้อมเวอร์ชันและวันที่อัปเดต
        self.root.title("🔍 BorderDetect & Metadata - V2.01 (Updated 22 Jan 2026)")
        
        # ปรับขนาดหน้าจอตามที่ต้องการ: 90% ของ 1680x1050 = 1680x945
        self.root.geometry("1680x945")
        
        # Store image hashes for duplicate detection
        self.image_hashes = {}
        
        # Processing queues
        self.left_queue = queue.Queue()
        self.right_queue = queue.Queue()
        self.result_queue = queue.Queue()
        
        # Processing state
        self.processing = False
        self.total_images = 0
        self.processed_images = 0
        self.selected_folder = None
        self.start_time = None
        
        # Keep track of the last processed image per category
        self.last_processed = {
            'Good': None,
            'Black': None,
            'White': None,
            'Duplicate': None
        }
        
        # Define categories (changed to 4 as requested)
        self.categories = {
            'good': 'Good',
            'black': 'Black',
            'white': 'White',
            'duplicate': 'Duplicate'
        }
        
        # Storage for each category manager
        self.category_managers = {
            'Good': {'groups': {}, 'selected': set(), 'checkboxes': {}, 'current_group': [], 'preview_index': 0},
            'Black': {'groups': {}, 'selected': set(), 'checkboxes': {}, 'current_group': [], 'preview_index': 0},
            'White': {'groups': {}, 'selected': set(), 'checkboxes': {}, 'current_group': [], 'preview_index': 0},
            'Duplicate': {'groups': {}, 'selected': set(), 'checkboxes': {}, 'current_group': [], 'preview_index': 0}
        }
        
        # Current gallery category
        self.current_gallery_category = None
        
        # Thumbnail cache for speed
        self._thumbnail_cache = {}
        
        # Create UI
        self.create_ui()
        
        # Start result processing thread
        threading.Thread(target=self.process_results, daemon=True).start()
        
        # Multiprocessing setup
        self.num_cores = max(1, multiprocessing.cpu_count() - 1)
        self.executor = None
        
        # Thread locks for thread safety
        self.hash_lock = threading.Lock()
        self.progress_lock = threading.Lock()
    
    def create_ui(self):
        """Create the user interface - single tab with gallery functionality"""
        # Main frame
        main_frame = ttk.Frame(self.root, padding=10)
        main_frame.pack(fill=BOTH, expand=YES)
        
        # Store main_frame reference
        self.main_frame = main_frame
        
        # Create the checker UI directly (no tabs needed now)
        self.create_checker_tab()
        
    def create_checker_tab(self):
        """Create the Image Checker interface with integrated gallery"""
        # Control section
        control_frame = ttk.Frame(self.main_frame)
        control_frame.pack(fill=X, pady=5)
        
        # Configure large button style (1.5x size)
        style = ttk.Style()
        style.configure('Large.TButton', font=('TkDefaultFont', 12, 'bold'), padding=(15, 10))
        
        # Folder selection button (wider to accommodate folder name)
        self.select_btn = ttk.Button(
            control_frame, 
            text="📂 Select Images Folder",
            command=self.select_folder,
            bootstyle="primary",
            style='Large.TButton',
            width=30
        )
        self.select_btn.pack(side=LEFT, padx=5)
        
        # Start/Stop button
        self.start_btn = ttk.Button(
            control_frame,
            text="▶ Start Processing",
            command=self.toggle_processing,
            bootstyle="success",
            style='Large.TButton'
        )
        self.start_btn.pack(side=LEFT, padx=5)
        
        # Merge & Split Files button (combined functionality)
        self.merge_split_btn = ttk.Button(
            control_frame,
            text="📁 Merge & Split Files",
            command=self.merge_and_split_files,
            bootstyle="warning",
            style='Large.TButton'
        )
        self.merge_split_btn.pack(side=LEFT, padx=5)
        
        # Clear Data button
        self.clear_btn = ttk.Button(
            control_frame,
            text="🗑 Clear",
            command=self.clear_all_data,
            bootstyle="secondary",
            style='Large.TButton'
        )
        self.clear_btn.pack(side=LEFT, padx=5)
        
        # Progress info
        self.progress_label = ttk.Label(control_frame, text="Processed 0 of 0 images")
        self.progress_label.pack(side=LEFT, padx=20)
        
        # Timer label
        self.timer_label = ttk.Label(control_frame, text="Time: 00:00:00")
        self.timer_label.pack(side=LEFT, padx=20)
        
        # Progress bar
        self.progress_bar = ttk.Progressbar(
            self.main_frame,
            bootstyle="success-striped",
            mode="determinate"
        )
        self.progress_bar.pack(fill=X, pady=5)
        
        # Image section titles (for check mode)
        self.title_frame = ttk.Frame(self.main_frame)
        self.title_frame.pack(fill=X, pady=5)
        
        # Left panel title
        ttk.Label(
            self.title_frame,
            text="ภาพเช็คด้านซ้าย",
            font=("TkDefaultFont", 14, "bold"),
            anchor=CENTER
        ).pack(side=LEFT, fill=X, expand=YES)
        
        # Right panel title
        ttk.Label(
            self.title_frame,
            text="ภาพเช็คด้านขวา",
            font=("TkDefaultFont", 14, "bold"),
            anchor=CENTER
        ).pack(side=LEFT, fill=X, expand=YES)
        
        # Main image display area (for check mode)
        self.image_frame = ttk.Frame(self.main_frame)
        self.image_frame.pack(fill=BOTH, expand=YES, pady=5)
        
        # Left image area
        self.left_frame = ttk.Frame(self.image_frame, bootstyle="info")
        self.left_frame.pack(side=LEFT, fill=BOTH, expand=YES, padx=5)
        self.left_img_label = ttk.Label(self.left_frame)
        self.left_img_label.pack(fill=BOTH, expand=YES)
        
        # Right image area
        self.right_frame = ttk.Frame(self.image_frame, bootstyle="info")
        self.right_frame.pack(side=LEFT, fill=BOTH, expand=YES, padx=5)
        self.right_img_label = ttk.Label(self.right_frame)
        self.right_img_label.pack(fill=BOTH, expand=YES)
        
        # ========== GALLERY FRAME (hidden initially) ==========
        self.gallery_frame = ttk.Frame(self.main_frame)
        # Don't pack yet - will be shown when category is clicked
        
        # Gallery header with controls
        self.gallery_header = ttk.Frame(self.gallery_frame)
        self.gallery_header.pack(fill=X, pady=5)
        
        # Back button
        ttk.Button(
            self.gallery_header,
            text="← กลับ",
            command=self.hide_category_gallery,
            bootstyle="secondary"
        ).pack(side=LEFT, padx=5)
        
        # Gallery title
        self.gallery_title = ttk.Label(
            self.gallery_header,
            text="",
            font=("TkDefaultFont", 16, "bold")
        )
        self.gallery_title.pack(side=LEFT, padx=20)
        
        # Refresh button
        ttk.Button(
            self.gallery_header,
            text="🔄 Refresh",
            command=lambda: self.load_category_thumbnails(self.current_gallery_category),
            bootstyle="info"
        ).pack(side=LEFT, padx=5)
        
        # Auto Mark / Unmark All toggle button
        self.auto_mark_btn = ttk.Button(
            self.gallery_header,
            text="✓ Auto Mark",
            command=self.toggle_auto_mark,
            bootstyle="primary"
        )
        self.auto_mark_btn.pack(side=LEFT, padx=5)
        
        # Remove selected button
        self.gallery_remove_btn = ttk.Button(
            self.gallery_header,
            text="🗑 Remove Selected (0)",
            command=self.remove_selected_gallery,
            bootstyle="danger"
        )
        self.gallery_remove_btn.pack(side=RIGHT, padx=20)
        
        # Gallery stats
        self.gallery_stats = ttk.Label(
            self.gallery_header,
            text="",
            font=("TkDefaultFont", 11)
        )
        self.gallery_stats.pack(side=RIGHT, padx=10)
        
        # Gallery content (scrollable thumbnails)
        gallery_content_frame = ttk.Frame(self.gallery_frame)
        gallery_content_frame.pack(fill=BOTH, expand=YES, pady=5)
        
        # Canvas with scrollbar for thumbnails
        self.gallery_canvas = tk.Canvas(gallery_content_frame, bg="#1a1a2e", highlightthickness=0)
        gallery_scrollbar = ttk.Scrollbar(gallery_content_frame, orient=VERTICAL, command=self.gallery_canvas.yview)
        self.gallery_scrollable = ttk.Frame(self.gallery_canvas)
        
        self.gallery_scrollable.bind(
            "<Configure>",
            lambda e: self.gallery_canvas.configure(scrollregion=self.gallery_canvas.bbox("all"))
        )
        
        self.gallery_canvas_window = self.gallery_canvas.create_window((0, 0), window=self.gallery_scrollable, anchor="nw")
        self.gallery_canvas.configure(yscrollcommand=gallery_scrollbar.set)
        
        # Mouse wheel binding
        self.gallery_canvas.bind("<MouseWheel>", lambda e: self.gallery_canvas.yview_scroll(int(-1*(e.delta/120)), "units"))
        self.gallery_canvas.bind("<Configure>", lambda e: self.gallery_canvas.itemconfig(self.gallery_canvas_window, width=e.width))
        
        gallery_scrollbar.pack(side=RIGHT, fill=Y)
        self.gallery_canvas.pack(side=LEFT, fill=BOTH, expand=YES)
        
        # ========== CATEGORY DISPLAY AREA (clickable) ==========
        results_frame = ttk.Frame(self.main_frame)
        results_frame.pack(fill=X, pady=5)
        
        # Create frames for each category
        self.category_frames = {}
        self.category_labels = {}
        self.category_title_labels = {}  # Store title labels for highlighting
        self.category_count_labels = {}  # Store count labels
        
        category_styles = {
            'Good': 'success',
            'Black': 'dark', 
            'White': 'light',
            'Duplicate': 'secondary'
        }
        
        # Store original styles for reset
        self.category_original_styles = category_styles.copy()
        
        for cat_name in self.categories.values():
            # Main frame for category (clickable)
            frame = ttk.Frame(
                results_frame,
                bootstyle=category_styles.get(cat_name, 'warning')
            )
            frame.pack(side=LEFT, fill=BOTH, expand=YES, padx=2)
            self.category_frames[cat_name] = frame
            
            # Make frame clickable
            frame.bind("<Button-1>", lambda e, cat=cat_name: self.show_category_gallery(cat))
            
            # Category label with count (on same line)
            cat_label = ttk.Label(
                frame,
                text=f"{cat_name} (0 ภาพ)",
                font=("TkDefaultFont", 14, "bold"),
                foreground="#FFFFFF",
                anchor=CENTER,
                cursor="hand2"
            )
            cat_label.pack(fill=X)
            cat_label.bind("<Button-1>", lambda e, cat=cat_name: self.show_category_gallery(cat))
            self.category_title_labels[cat_name] = cat_label
            self.category_count_labels[cat_name] = cat_label  # Same label for both
            
            # Image preview (clickable)
            preview = ttk.Label(frame, cursor="hand2")
            preview.pack(fill=BOTH, expand=YES, pady=5)
            preview.bind("<Button-1>", lambda e, cat=cat_name: self.show_category_gallery(cat))
            self.category_labels[cat_name] = preview
    
    # ==================== GALLERY METHODS ====================
    
    def show_category_gallery(self, category):
        """Show thumbnails for selected category, hide check panels"""
        if not self.selected_folder:
            messagebox.showinfo("ไม่พบโฟลเดอร์", "กรุณาเลือกโฟลเดอร์ก่อน")
            return
        
        # Hide check panels (left/right image areas)
        self.image_frame.pack_forget()
        self.title_frame.pack_forget()
        
        # Show gallery frame (insert before results_frame)
        self.gallery_frame.pack(fill=BOTH, expand=YES, pady=5, before=self.category_frames['Good'].master)
        
        # Update current category
        self.current_gallery_category = category
        
        # Highlight selected category
        self._highlight_category(category)
        
        # Update title
        self.gallery_title.config(text=f"📁 {category}")
        
        # Load thumbnails
        self.load_category_thumbnails(category)
        
        # Auto mark for non-Good categories
        if category != 'Good':
            self.root.after(100, lambda: self.auto_mark_category(category))
    
    def hide_category_gallery(self):
        """Hide gallery and show check panels"""
        self.gallery_frame.pack_forget()
        
        # Get the category results frame for reference
        results_frame = self.category_frames['Good'].master
        
        # Pack title_frame and image_frame before results_frame
        self.title_frame.pack(fill=X, pady=5, before=results_frame)
        self.image_frame.pack(fill=BOTH, expand=YES, pady=5, before=results_frame)
        
        # Reset category highlighting
        self._reset_category_highlights()
        
        self.current_gallery_category = None
    
    def _highlight_category(self, category):
        """Highlight the selected category frame"""
        # Reset all categories first
        self._reset_category_highlights()
        
        # Highlight selected category with warning style (yellow/orange)
        if category in self.category_frames:
            self.category_frames[category].configure(bootstyle="warning")
            if category in self.category_title_labels:
                # Keep text WHITE and add underline to show selection
                self.category_title_labels[category].configure(foreground="#FFFFFF", font=("TkDefaultFont", 14, "bold underline"))
    
    def _reset_category_highlights(self):
        """Reset all category frame styles to original"""
        for cat_name, frame in self.category_frames.items():
            original_style = self.category_original_styles.get(cat_name, 'secondary')
            frame.configure(bootstyle=original_style)
            if cat_name in self.category_title_labels:
                # Keep text WHITE when resetting
                self.category_title_labels[cat_name].configure(foreground="#FFFFFF", font=("TkDefaultFont", 14, "bold"))
    
    def update_category_counts(self):
        """Update the image count display for all categories"""
        if not self.selected_folder:
            return
        
        image_extensions = ('.jpg', '.jpeg', '.png', '.tif', '.tiff', '.bmp')
        
        for cat_name in self.categories.values():
            folder = os.path.join(self.selected_folder, cat_name)
            if os.path.exists(folder):
                count = len([f for f in os.listdir(folder) 
                            if f.lower().endswith(image_extensions) and os.path.isfile(os.path.join(folder, f))])
            else:
                count = 0
            
            if cat_name in self.category_count_labels:
                self.category_count_labels[cat_name].config(text=f"{cat_name} ({count} ภาพ)")
    
    def _refresh_category_previews(self):
        """Refresh preview images for all categories"""
        if not self.selected_folder:
            return
        
        image_extensions = ('.jpg', '.jpeg', '.png', '.tif', '.tiff', '.bmp')
        
        for cat_name in self.categories.values():
            folder = os.path.join(self.selected_folder, cat_name)
            
            # Clear current preview
            if cat_name in self.category_labels:
                self.category_labels[cat_name].config(image='')
                self.category_labels[cat_name].image_tk = None
            
            # Load first image as preview if folder has images
            if os.path.exists(folder):
                images = [f for f in os.listdir(folder) 
                         if f.lower().endswith(image_extensions) and os.path.isfile(os.path.join(folder, f))]
                
                if images:
                    first_img = os.path.join(folder, images[0])
                    try:
                        img = imread_unicode(first_img)
                        if img is not None:
                            thumb = self.resize_image(img, 200, 150)
                            thumb_tk = ImageTk.PhotoImage(Image.fromarray(thumb))
                            self.category_labels[cat_name].config(image=thumb_tk)
                            self.category_labels[cat_name].image_tk = thumb_tk
                    except:
                        pass
    
    def load_category_thumbnails(self, category):
        """Load thumbnails with fast loading"""
        # Clear existing thumbnails
        for widget in self.gallery_scrollable.winfo_children():
            widget.destroy()
        
        # Reset manager
        manager = self.category_managers[category]
        manager['selected'] = set()
        manager['checkboxes'] = {}
        
        # Get images from folder
        folder = os.path.join(self.selected_folder, category)
        good_folder = os.path.join(self.selected_folder, "Good")
        image_extensions = ('.jpg', '.jpeg', '.png', '.tif', '.tiff', '.bmp')
        images = []
        
        if os.path.exists(folder):
            images = [os.path.join(folder, f) for f in os.listdir(folder) 
                      if f.lower().endswith(image_extensions) and os.path.isfile(os.path.join(folder, f))]
        
        # For Duplicate: ALSO scan Good folder to find matching pairs
        if category == 'Duplicate':
            good_images = []
            if os.path.exists(good_folder):
                good_images = [os.path.join(good_folder, f) for f in os.listdir(good_folder) 
                              if f.lower().endswith(image_extensions) and os.path.isfile(os.path.join(good_folder, f))]
            
            # Combine both folders for similarity matching
            all_images = images + good_images
            
            if not all_images:
                self.gallery_stats.config(text=f"ไม่พบภาพใน {category}")
                self._update_gallery_remove_button()
                return
            
            self._create_grouped_display(category, all_images)
        else:
            if not images:
                self.gallery_stats.config(text=f"ไม่พบภาพใน {category}")
                self._update_gallery_remove_button()
                return
            
            # Sort and show flat grid for other categories
            images.sort(key=lambda x: self._get_sort_key(x))
            self.gallery_stats.config(text=f"พบ {len(images)} ภาพ")
            self._create_thumbnail_grid(category, images)
        
        self._update_gallery_remove_button()
    
    def _create_grouped_display(self, category, images):
        """Create grouped display for Duplicate category"""
        manager = self.category_managers[category]
        duplicate_folder = os.path.join(self.selected_folder, "Duplicate")
        good_folder = os.path.join(self.selected_folder, "Good")
        
        # Group images by visual similarity
        groups = self._group_duplicates_by_similarity(images)
        groups = [g for g in groups if len(g) >= 2]  # Only show groups with 2+ images
        
        if not groups:
            self.gallery_stats.config(text="ไม่พบภาพที่ซ้ำกัน")
            return
        
        # Collect files to move
        files_to_move = []
        for group in groups:
            for img_path in group:
                if good_folder in img_path:
                    files_to_move.append(img_path)
        
        # Move files in parallel for better performance
        moved_files = {}  # old_path -> new_path
        if files_to_move:
            os.makedirs(duplicate_folder, exist_ok=True)
            
            def move_file(img_path):
                filename = os.path.basename(img_path)
                new_path = os.path.join(duplicate_folder, filename)
                
                # Handle name conflicts
                if os.path.exists(new_path):
                    name, ext = os.path.splitext(filename)
                    counter = 1
                    while os.path.exists(new_path):
                        new_path = os.path.join(duplicate_folder, f"{name}_{counter}{ext}")
                        counter += 1
                
                try:
                    shutil.move(img_path, new_path)
                    return (img_path, new_path)
                except Exception as e:
                    return (img_path, img_path)  # Keep original on error
            
            from concurrent.futures import ThreadPoolExecutor
            with ThreadPoolExecutor(max_workers=8) as executor:
                results = list(executor.map(move_file, files_to_move))
            
            for old_path, new_path in results:
                moved_files[old_path] = new_path
        
        # Update groups with new paths
        updated_groups = []
        for group in groups:
            updated_group = []
            for img_path in group:
                if img_path in moved_files:
                    updated_group.append(moved_files[img_path])
                else:
                    updated_group.append(img_path)
            updated_groups.append(updated_group)
        
        groups = updated_groups
        moved_count = len([p for p in moved_files.values() if p != moved_files.get(p, p)])
        
        # Update category counts AND preview images after moving
        if moved_count > 0:
            self.update_category_counts()
            self._refresh_category_previews()
        
        total_images = sum(len(g) for g in groups)
        self.gallery_stats.config(text=f"พบ {total_images} ภาพใน {len(groups)} กลุ่ม (ย้าย {len(files_to_move)} ภาพ)")
        
        # Store pending thumbnails for async loading
        pending_thumbnails = []
        
        for group_idx, group in enumerate(groups, 1):
            # Group header
            header_frame = ttk.Frame(self.gallery_scrollable)
            header_frame.pack(fill=X, padx=10, pady=(15, 5))
            
            ttk.Label(
                header_frame, 
                text=f"Group {group_idx}",
                font=("TkDefaultFont", 12, "bold"),
                foreground="#4dabf7"
            ).pack(anchor=W)
            
            # Separator line
            ttk.Separator(self.gallery_scrollable, orient=HORIZONTAL).pack(fill=X, padx=10, pady=2)
            
            # Images row for this group
            row_frame = ttk.Frame(self.gallery_scrollable)
            row_frame.pack(fill=X, padx=10, pady=5)
            
            for img_path in group:
                # Create thumbnail frame
                thumb_frame = ttk.Frame(row_frame)
                thumb_frame.pack(side=LEFT, padx=5, pady=3)
                
                # Checkbox
                var = tk.BooleanVar(value=False)
                manager['checkboxes'][img_path] = var
                
                cb = ttk.Checkbutton(
                    thumb_frame,
                    variable=var,
                    command=lambda p=img_path: self._on_gallery_checkbox_toggle(p),
                    bootstyle="primary-round-toggle"
                )
                cb.pack(anchor=NE)
                
                # Placeholder for fast initial display
                thumb_label = ttk.Label(thumb_frame, text="⏳", width=12, anchor=CENTER, cursor="hand2")
                thumb_label.pack()
                
                # Filename
                filename = os.path.basename(img_path)
                is_copy = 'copy' in filename.lower()
                display_name = filename[:18] + "..." if len(filename) > 21 else filename
                
                name_label = ttk.Label(thumb_frame, text=display_name, font=("TkDefaultFont", 8))
                if is_copy:
                    name_label.config(foreground="#ff6b6b")  # Red for copies
                name_label.pack()
                
                # File info
                try:
                    stat = os.stat(img_path)
                    mtime = datetime.datetime.fromtimestamp(stat.st_mtime).strftime("%d/%m/%Y")
                    ttk.Label(thumb_frame, text=f"{mtime}, {self._format_size(stat.st_size)}", 
                              font=("TkDefaultFont", 8), foreground="#888888").pack()
                except:
                    pass
                
                # Add to pending for async loading
                pending_thumbnails.append((thumb_label, img_path, category, group))
                
                # Auto-mark if filename contains 'copy'
                if is_copy:
                    var.set(True)
                    manager['selected'].add(img_path)
        
        # Update UI immediately with placeholders
        self.root.update_idletasks()
        
        # Load thumbnails in background thread
        if pending_thumbnails:
            threading.Thread(
                target=self._load_grouped_thumbnails,
                args=(pending_thumbnails,),
                daemon=True
            ).start()
    
    def _load_grouped_thumbnails(self, pending_list):
        """Load thumbnails for grouped display in background"""
        from concurrent.futures import ThreadPoolExecutor
        
        def load_single(item):
            thumb_label, img_path, category, group = item
            try:
                if img_path in self._thumbnail_cache:
                    return (thumb_label, self._thumbnail_cache[img_path], img_path, category, group)
                
                img = imread_unicode(img_path)
                if img is not None:
                    thumb = self.resize_image(img, 100, 80)
                    return (thumb_label, thumb, img_path, category, group)
            except:
                pass
            return (thumb_label, None, img_path, category, group)
        
        # Load in parallel
        with ThreadPoolExecutor(max_workers=8) as executor:
            results = list(executor.map(load_single, pending_list))
        
        # Update UI from main thread
        for thumb_label, thumb_data, img_path, category, group in results:
            try:
                if thumb_data is None:
                    self.root.after(0, lambda l=thumb_label: l.config(text="❌") if l.winfo_exists() else None)
                    continue
                
                if isinstance(thumb_data, ImageTk.PhotoImage):
                    thumb_tk = thumb_data
                else:
                    thumb_tk = ImageTk.PhotoImage(Image.fromarray(thumb_data))
                    self._thumbnail_cache[img_path] = thumb_tk
                
                def update_ui(label, image, path, cat, grp):
                    if label.winfo_exists():
                        label.config(image=image, text="")
                        label.image_tk = image
                        label.bind("<Button-1>", lambda e, p=path, g=grp: self._on_gallery_thumbnail_click(cat, p, g))
                
                self.root.after(0, lambda l=thumb_label, i=thumb_tk, p=img_path, c=category, g=group: update_ui(l, i, p, c, g))
            except:
                pass
    
    def _create_thumbnail_grid(self, category, images):
        """Create thumbnail grid with lazy loading for fast display"""
        manager = self.category_managers[category]
        
        # Create rows
        row_frame = None
        col = 0
        max_cols = 10
        
        # Store pending thumbnails for batch loading
        pending_thumbnails = []
        
        for img_path in images:
            # Create new row if needed
            if col == 0 or col >= max_cols:
                row_frame = ttk.Frame(self.gallery_scrollable)
                row_frame.pack(fill=X, padx=5, pady=2)
                col = 0
            
            # Create thumbnail frame
            thumb_frame = ttk.Frame(row_frame)
            thumb_frame.pack(side=LEFT, padx=3, pady=3)
            
            # Checkbox
            var = tk.BooleanVar(value=False)
            manager['checkboxes'][img_path] = var
            
            cb = ttk.Checkbutton(
                thumb_frame,
                variable=var,
                command=lambda p=img_path: self._on_gallery_checkbox_toggle(p),
                bootstyle="primary-round-toggle"
            )
            cb.pack(anchor=NE)
            
            # Create placeholder label first (instant display)
            thumb_label = ttk.Label(thumb_frame, text="⏳", width=12, anchor=CENTER, cursor="hand2")
            thumb_label.pack()
            
            # Filename (show immediately)
            filename = os.path.basename(img_path)
            is_copy = 'copy' in filename.lower()
            display_name = filename[:12] + "..." if len(filename) > 15 else filename
            
            name_label = ttk.Label(thumb_frame, text=display_name, font=("TkDefaultFont", 8))
            if is_copy:
                name_label.config(foreground="#ff6b6b")
            name_label.pack()
            
            # File size (show immediately - fast operation)
            try:
                size = os.path.getsize(img_path)
                ttk.Label(thumb_frame, text=self._format_size(size), font=("TkDefaultFont", 8)).pack()
            except:
                pass
            
            # Add to pending list for background loading
            pending_thumbnails.append((thumb_label, img_path, category))
            
            col += 1
        
        # Update UI immediately, then load images in background
        self.root.update_idletasks()
        
        # Start background thread to load thumbnails
        if pending_thumbnails:
            threading.Thread(
                target=self._load_thumbnails_batch,
                args=(pending_thumbnails,),
                daemon=True
            ).start()
    
    def _load_thumbnails_batch(self, pending_list):
        """Load thumbnails in background using multiple threads for speed"""
        from concurrent.futures import ThreadPoolExecutor
        
        def load_single_thumbnail(item):
            thumb_label, img_path, category = item
            try:
                # Check cache first (fast path)
                cache_key = img_path
                if cache_key in self._thumbnail_cache:
                    return (thumb_label, self._thumbnail_cache[cache_key], img_path, category, True)
                
                # Load and resize image
                img = imread_unicode(img_path)
                if img is None:
                    return (thumb_label, None, img_path, category, False)
                
                thumb = self.resize_image(img, 100, 75)
                return (thumb_label, thumb, img_path, category, True)
                
            except Exception as e:
                return (thumb_label, None, img_path, category, False)
        
        def update_ui(result):
            thumb_label, thumb_data, img_path, category, success = result
            try:
                if not thumb_label.winfo_exists():
                    return
                
                if not success or thumb_data is None:
                    thumb_label.config(text="❌")
                    return
                
                # Check if already PhotoImage (from cache) or numpy array
                if isinstance(thumb_data, ImageTk.PhotoImage):
                    thumb_tk = thumb_data
                else:
                    thumb_tk = ImageTk.PhotoImage(Image.fromarray(thumb_data))
                    self._thumbnail_cache[img_path] = thumb_tk
                
                thumb_label.config(image=thumb_tk, text="")
                thumb_label.image_tk = thumb_tk
                
                # Bind click event
                manager = self.category_managers[category]
                all_images = list(manager['checkboxes'].keys())
                thumb_label.bind("<Button-1>", lambda e, p=img_path, g=all_images: self._on_gallery_thumbnail_click(category, p, g))
            except:
                pass
        
        # Use ThreadPoolExecutor for concurrent loading (8 workers for speed)
        with ThreadPoolExecutor(max_workers=8) as executor:
            results = executor.map(load_single_thumbnail, pending_list)
            
            # Update UI as results come in
            for result in results:
                self.root.after(0, lambda r=result: update_ui(r))
    
    def _on_gallery_thumbnail_click(self, category, img_path, group):
        """Handle thumbnail click in gallery - open fullscreen viewer"""
        manager = self.category_managers[category]
        manager['current_group'] = group
        manager['preview_index'] = group.index(img_path) if img_path in group else 0
        self._open_fullscreen_viewer(category)
    
    def _on_gallery_checkbox_toggle(self, img_path):
        """Handle checkbox toggle in gallery"""
        category = self.current_gallery_category
        if not category:
            return
        
        manager = self.category_managers[category]
        var = manager['checkboxes'].get(img_path)
        if var:
            if var.get():
                manager['selected'].add(img_path)
            else:
                manager['selected'].discard(img_path)
        
        self._update_gallery_remove_button()
        self._update_auto_mark_button()
    
    def _update_gallery_remove_button(self):
        """Update gallery remove button text"""
        category = self.current_gallery_category
        if not category:
            return
        
        manager = self.category_managers[category]
        count = len(manager['selected'])
        total_size = sum(os.path.getsize(f) for f in manager['selected'] if os.path.exists(f))
        self.gallery_remove_btn.config(
            text=f"🗑 Remove Selected ({count}) - {self._format_size(total_size)}"
        )
    
    def _update_auto_mark_button(self):
        """Update auto mark button based on current state"""
        category = self.current_gallery_category
        if not category:
            return
        
        manager = self.category_managers[category]
        total_checkboxes = len(manager['checkboxes'])
        selected_count = len(manager['selected'])
        
        if selected_count > 0 and selected_count == total_checkboxes:
            self.auto_mark_btn.config(text="✗ Unmark All", bootstyle="secondary")
        else:
            self.auto_mark_btn.config(text="✓ Auto Mark", bootstyle="primary")
    
    def toggle_auto_mark(self):
        """Toggle between Auto Mark and Unmark All"""
        category = self.current_gallery_category
        if not category:
            return
        
        manager = self.category_managers[category]
        total_checkboxes = len(manager['checkboxes'])
        selected_count = len(manager['selected'])
        
        if selected_count > 0 and selected_count == total_checkboxes:
            # All selected - unmark all
            self.unmark_all_category(category)
        else:
            # Not all selected - auto mark
            self.auto_mark_category(category)
        
        self._update_auto_mark_button()
        self._update_gallery_remove_button()
    
    def auto_mark_category(self, category):
        """Auto mark all images in category for deletion"""
        manager = self.category_managers[category]
        
        # Wait a bit for checkboxes to be created if loading
        if not manager['checkboxes']:
            # Retry after delay if checkboxes not yet created
            self.root.after(200, lambda: self.auto_mark_category(category))
            return
        
        # Mark all checkboxes
        for img_path, var in manager['checkboxes'].items():
            var.set(True)
            manager['selected'].add(img_path)
        
        self._update_gallery_remove_button()
        self._update_auto_mark_button()
    
    def unmark_all_category(self, category):
        """Unmark all images in category"""
        manager = self.category_managers[category]
        
        # Unmark all checkboxes
        for img_path, var in manager['checkboxes'].items():
            var.set(False)
        
        manager['selected'].clear()
        
        self._update_gallery_remove_button()
        self._update_auto_mark_button()
    
    def remove_selected_gallery(self):
        """Remove selected files from gallery"""
        category = self.current_gallery_category
        if not category:
            return
        
        manager = self.category_managers[category]
        
        if not manager['selected']:
            return
        
        count = len(manager['selected'])
        if messagebox.askyesno("ยืนยันการลบ", f"ต้องการลบ {count} ภาพที่เลือกใช่หรือไม่?"):
            deleted = 0
            for path in list(manager['selected']):
                try:
                    os.remove(path)
                    deleted += 1
                    # Clear from cache
                    if path in self._thumbnail_cache:
                        del self._thumbnail_cache[path]
                except Exception as e:
                    print(f"Error deleting {path}: {e}")
            
            messagebox.showinfo("เสร็จสิ้น", f"ลบไฟล์แล้ว {deleted} ไฟล์")
            self.load_category_thumbnails(category)
    
    def merge_and_split_files(self):
        """Combined Merge + Split operation - streamlined flow"""
        if not self.selected_folder:
            messagebox.showinfo("ไม่พบโฟลเดอร์", "กรุณาเลือกโฟลเดอร์ก่อน")
            return
        
        # Check if processing is ongoing
        if self.processing:
            messagebox.showwarning("กำลังประมวลผล", "กรุณารอให้การประมวลผลเสร็จสิ้นก่อน")
            return
        
        # First: Merge files (no success message)
        merged_folder = self._do_merge_files_silent()
        
        if merged_folder:
            # Directly ask how many files per folder and split
            self._quick_split_dialog(merged_folder)
    
    def _do_merge_files_silent(self):
        """Merge files silently and return the folder path if successful"""
        # Category folders to merge
        category_folders = ['Black', 'Duplicate', 'Good', 'White']
        
        # Count files to move
        files_to_move = []
        for cat in category_folders:
            cat_folder = os.path.join(self.selected_folder, cat)
            if os.path.exists(cat_folder):
                for f in os.listdir(cat_folder):
                    filepath = os.path.join(cat_folder, f)
                    if os.path.isfile(filepath):
                        files_to_move.append((filepath, f, cat))
        
        if not files_to_move:
            messagebox.showinfo("ไม่มีไฟล์", "ไม่พบไฟล์ในโฟลเดอร์ย่อย")
            return None
        
        # Move files silently
        for filepath, filename, category in files_to_move:
            dest_path = os.path.join(self.selected_folder, filename)
            
            # Handle name conflicts
            if os.path.exists(dest_path):
                name, ext = os.path.splitext(filename)
                counter = 1
                while os.path.exists(dest_path):
                    new_name = f"{name}_{counter}{ext}"
                    dest_path = os.path.join(self.selected_folder, new_name)
                    counter += 1
            
            try:
                shutil.move(filepath, dest_path)
            except Exception as e:
                print(f"Error moving {filename}: {e}")
        
        # Remove empty category folders
        for cat in category_folders:
            cat_folder = os.path.join(self.selected_folder, cat)
            if os.path.exists(cat_folder):
                try:
                    if not os.listdir(cat_folder):
                        os.rmdir(cat_folder)
                except:
                    pass
        
        # Return the folder path for splitting
        merged_folder = self.selected_folder
        
        # Clear all data
        self.clear_all_data()
        
        return merged_folder
    
    def _quick_split_dialog(self, source_folder):
        """Quick dialog to ask files per folder and split immediately"""
        # Count total files
        image_extensions = ('.jpg', '.jpeg', '.png', '.tif', '.tiff', '.bmp', '.gif', '.webp')
        files = [f for f in os.listdir(source_folder) 
                 if f.lower().endswith(image_extensions) and os.path.isfile(os.path.join(source_folder, f))]
        
        if not files:
            messagebox.showinfo("ไม่มีไฟล์", "ไม่พบไฟล์ภาพในโฟลเดอร์")
            return
        
        total_files = len(files)
        
        # Create simple dialog
        dialog = tk.Toplevel(self.root)
        dialog.title("แบ่งไฟล์")
        dialog.geometry("350x220")
        dialog.transient(self.root)
        dialog.grab_set()
        
        # Center dialog
        dialog.update_idletasks()
        x = (dialog.winfo_screenwidth() - 350) // 2
        y = (dialog.winfo_screenheight() - 220) // 2
        dialog.geometry(f"+{x}+{y}")
        
        # Info label
        ttk.Label(dialog, text=f"พบ {total_files} ไฟล์ในโฟลเดอร์", font=("TkDefaultFont", 11)).pack(pady=10)
        
        # Files per folder input
        input_frame = ttk.Frame(dialog)
        input_frame.pack(pady=10)
        
        ttk.Label(input_frame, text="จำนวนไฟล์ต่อโฟลเดอร์:").pack(side=LEFT, padx=5)
        files_var = tk.StringVar(value="500")
        files_entry = ttk.Entry(input_frame, textvariable=files_var, width=10)
        files_entry.pack(side=LEFT, padx=5)
        files_entry.select_range(0, tk.END)
        files_entry.focus()
        
        # Estimate label
        estimate_label = ttk.Label(dialog, text="", font=("TkDefaultFont", 10))
        estimate_label.pack(pady=5)
        
        def update_estimate(*args):
            try:
                max_per = int(files_var.get())
                if max_per > 0:
                    num_folders = math.ceil(total_files / max_per)
                    estimate_label.config(text=f"จะแบ่งเป็น {num_folders} โฟลเดอร์")
            except:
                estimate_label.config(text="")
        
        files_var.trace('w', update_estimate)
        update_estimate()
        
        def do_split():
            try:
                max_per_folder = int(files_var.get())
                if max_per_folder <= 0:
                    return
            except:
                return
            
            dialog.destroy()
            
            # Sort files
            files.sort()
            
            # Get folder base name for auto-naming
            folder_name = os.path.basename(source_folder)
            
            # Split files
            folder_num = 1
            for i in range(0, len(files), max_per_folder):
                batch = files[i:i+max_per_folder]
                
                # Auto-name: FolderName_01, FolderName_02, etc.
                new_folder_name = f"{folder_name}_{folder_num:02d}"
                new_folder_path = os.path.join(source_folder, new_folder_name)
                os.makedirs(new_folder_path, exist_ok=True)
                
                for filename in batch:
                    src = os.path.join(source_folder, filename)
                    dst = os.path.join(new_folder_path, filename)
                    try:
                        shutil.move(src, dst)
                    except Exception as e:
                        print(f"Error moving {filename}: {e}")
                
                folder_num += 1
            
            messagebox.showinfo("เสร็จสิ้น", f"แบ่งไฟล์เป็น {folder_num - 1} โฟลเดอร์เรียบร้อย")
        
        # Buttons
        btn_frame = ttk.Frame(dialog)
        btn_frame.pack(pady=15)
        
        ttk.Button(btn_frame, text="แบ่งไฟล์", command=do_split, bootstyle="success").pack(side=LEFT, padx=10)
        ttk.Button(btn_frame, text="ยกเลิก", command=dialog.destroy, bootstyle="secondary").pack(side=LEFT, padx=10)
        
        # Enter key to submit
        dialog.bind('<Return>', lambda e: do_split())
    
    def clear_all_data(self):
        """Clear all data and reset UI to initial state"""
        # Hide gallery if shown
        if self.current_gallery_category:
            self.hide_category_gallery()
        
        # Reset folder selection
        self.selected_folder = None
        self.select_btn.config(text="📂 Select Images Folder")
        
        # Clear hash data
        self.image_hashes = {}
        self._thumbnail_cache = {}
        if hasattr(self, '_hash_cache'):
            self._hash_cache = {}
        
        # Clear queues
        while not self.left_queue.empty():
            try:
                self.left_queue.get_nowait()
            except:
                break
        while not self.right_queue.empty():
            try:
                self.right_queue.get_nowait()
            except:
                break
        
        # Reset category managers
        for cat in self.category_managers:
            self.category_managers[cat] = {
                'groups': {}, 'selected': set(), 'checkboxes': {}, 
                'current_group': [], 'preview_index': 0
            }
        
        # Clear category previews and counts
        for cat_name in self.categories.values():
            if cat_name in self.category_labels:
                self.category_labels[cat_name].config(image='')
            if cat_name in self.category_count_labels:
                self.category_count_labels[cat_name].config(text="(0 ภาพ)")
        
        # Reset processing state
        self.total_images = 0
        self.processed_images = 0
        self.processing = False
        self.start_time = None
        
        # Reset last processed
        self.last_processed = {
            'Good': None,
            'Black': None,
            'White': None,
            'Duplicate': None
        }
        
        # Reset UI elements
        self.progress_label.config(text="Processed 0 of 0 images")
        self.progress_bar["value"] = 0
        self.progress_bar["maximum"] = 0
        self.timer_label.config(text="Time: 00:00:00")
        self.start_btn.config(text="▶ Start Processing", bootstyle="success")
        
        # Clear image displays
        self.left_img_label.config(image='')
        self.right_img_label.config(image='')
        
        # Reset highlights
        self._reset_category_highlights()
    
    def _cycle_preview(self, category):
        """Cycle to next image in current group when clicking preview"""
        manager = self.category_managers.get(category, {})
        current_group = manager.get('current_group', [])
        
        if not current_group:
            return
        
        # Increment index
        idx = manager.get('preview_index', 0)
        idx = (idx + 1) % len(current_group)
        manager['preview_index'] = idx
        
        # Show the image
        self._show_category_preview(category, current_group[idx])
    
    def refresh_category_groups(self, category):
        """Load and display image groups for a category (Black/White/Duplicate)"""
        if not self.selected_folder:
            self.cat_ui[category]['stats_label'].config(text="กรุณาเลือกโฟลเดอร์และเริ่มการตรวจสอบก่อน")
            return
        
        # Get the category folder
        category_folder = os.path.join(self.selected_folder, category)
        good_folder = os.path.join(self.selected_folder, "Good")
        
        # Clear existing display
        scrollable_frame = self.cat_ui[category]['scrollable_frame']
        for widget in scrollable_frame.winfo_children():
            widget.destroy()
        
        # Clear thumbs_frame cache for Black/White so new one is created
        if hasattr(self, '_category_thumbs_frame') and category in self._category_thumbs_frame:
            del self._category_thumbs_frame[category]
        
        manager = self.category_managers[category]
        manager['groups'] = {}
        manager['selected'] = set()
        manager['checkboxes'] = {}
        
        # Find images in category folder and Good folder
        image_extensions = ('.jpg', '.jpeg', '.png', '.tif', '.tiff', '.bmp')
        all_images = []
        
        if os.path.exists(category_folder):
            for f in os.listdir(category_folder):
                if f.lower().endswith(image_extensions):
                    filepath = os.path.join(category_folder, f)
                    if os.path.isfile(filepath):
                        all_images.append(filepath)
        
        # For Duplicate, also scan Good folder
        if category == 'Duplicate' and os.path.exists(good_folder):
            for f in os.listdir(good_folder):
                if f.lower().endswith(image_extensions):
                    filepath = os.path.join(good_folder, f)
                    if os.path.isfile(filepath):
                        all_images.append(filepath)
        
        if not all_images:
            self.cat_ui[category]['stats_label'].config(text=f"ไม่พบภาพในโฟลเดอร์ {category}")
            return
        
        self.cat_ui[category]['stats_label'].config(text="กำลังวิเคราะห์ภาพ...")
        self.root.update()
        
        # For Duplicate: Group by similarity | For Black/White: Show all as single group
        if category == 'Duplicate':
            groups = self._group_duplicates_by_similarity(all_images)
            # Filter to only groups with 2+ images
            groups = [g for g in groups if len(g) >= 2]
        else:
            # Black/White: each image is its own group (no similarity needed)
            groups = [[img] for img in all_images]
        
        if not groups:
            self.cat_ui[category]['stats_label'].config(text=f"ไม่พบภาพใน {category}")
            return
        
        # Sort each group: original first, copy last
        for group in groups:
            group.sort(key=lambda x: self._get_sort_key(x))
        
        # Stats
        total_images = sum(len(g) for g in groups)
        total_size = sum(os.path.getsize(f) for g in groups for f in g if os.path.exists(f))
        
        # Stats - different text for Black/White vs Duplicate
        if category in ('Black', 'White'):
            self.cat_ui[category]['stats_label'].config(
                text=f"พบ {total_images} ภาพ - รวม: {self._format_size(total_size)}"
            )
        else:
            self.cat_ui[category]['stats_label'].config(
                text=f"พบ {total_images} ภาพใน {len(groups)} กลุ่ม - รวม: {self._format_size(total_size)}"
            )
        
        # Display groups
        for i, group in enumerate(groups):
            self._create_category_group_ui(category, i + 1, group)
        
        self._update_category_remove_button(category)
    
    def _get_sort_key(self, filepath):
        """Sort key: Original files first, Copy/numbered files last"""
        filename = os.path.basename(filepath).lower()
        # Files with 'copy', '_1', '_2', etc. go last
        if 'copy' in filename or ' - copy' in filename:
            return (1, filename)
        # Check for numbered suffixes like _1, _2, (1), (2)
        if re.search(r'[\(_]\d+[\)_]?\.[a-z]+$', filename):
            return (1, filename)
        return (0, filename)
    
    def _group_duplicates_by_similarity(self, images):
        """Group images by visual similarity using perceptual hash"""
        if not images:
            return []
        
        # Initialize hash cache if not exists
        if not hasattr(self, '_hash_cache'):
            self._hash_cache = {}
        
        # Calculate hashes - use cache when available
        image_hashes = {}
        images_to_hash = []
        
        for img_path in images:
            # Check cache first (use file path + modification time as key)
            try:
                mtime = os.path.getmtime(img_path)
                cache_key = (img_path, mtime)
                
                if cache_key in self._hash_cache:
                    image_hashes[img_path] = self._hash_cache[cache_key]
                else:
                    images_to_hash.append((img_path, cache_key))
            except:
                images_to_hash.append((img_path, None))
        
        # Parallel hash calculation for uncached images
        if images_to_hash:
            from concurrent.futures import ThreadPoolExecutor
            
            def compute_hash(item):
                img_path, cache_key = item
                try:
                    img, _ = prepare_image(img_path)
                    if img is not None:
                        pil_img = Image.fromarray(cv2.cvtColor(img, cv2.COLOR_BGR2RGB))
                        if pil_img.mode != 'RGB':
                            pil_img = pil_img.convert('RGB')
                        hash_val = imagehash.phash(pil_img, hash_size=HASH_SIZE)
                        return img_path, hash_val, cache_key
                except Exception as e:
                    print(f"Error hashing {img_path}: {e}")
                return img_path, None, cache_key
            
            # Use thread pool for I/O-bound operations
            with ThreadPoolExecutor(max_workers=8) as executor:
                results = list(executor.map(compute_hash, images_to_hash))
            
            for img_path, hash_val, cache_key in results:
                if hash_val is not None:
                    image_hashes[img_path] = hash_val
                    # Cache the result
                    if cache_key:
                        self._hash_cache[cache_key] = hash_val
        
        # Group by similarity
        used = set()
        groups = []
        
        for path1, hash1 in image_hashes.items():
            if path1 in used:
                continue
            
            group = [path1]
            used.add(path1)
            
            for path2, hash2 in image_hashes.items():
                if path2 in used:
                    continue
                
                distance = hash1 - hash2
                if distance <= SIMILARITY_THRESHOLD:
                    group.append(path2)
                    used.add(path2)
            
            groups.append(group)
        
        return groups
    
    def _create_category_group_ui(self, category, group_id, images):
        """Create UI for a group in category manager"""
        scrollable_frame = self.cat_ui[category]['scrollable_frame']
        manager = self.category_managers[category]
        
        # For Black/White: no group frame, just place thumbnails directly (no grouping)
        # For Duplicate: use group frame to show related images
        if category in ('Black', 'White'):
            # No grouping - create thumbnails frame directly in scrollable_frame
            if not hasattr(self, '_category_thumbs_frame'):
                self._category_thumbs_frame = {}
            
            # Create one shared thumbnails frame per category (created once)
            if category not in self._category_thumbs_frame:
                thumbs_frame = ttk.Frame(scrollable_frame)
                thumbs_frame.pack(fill=X, padx=5, pady=5)
                self._category_thumbs_frame[category] = thumbs_frame
            else:
                thumbs_frame = self._category_thumbs_frame[category]
            
            for img_path in images:
                self._create_category_thumbnail_ui(category, thumbs_frame, img_path, images)
        else:
            # Duplicate: use group frame with header
            group_frame = ttk.LabelFrame(
                scrollable_frame,
                text=f"Group {group_id}",
                bootstyle="info"
            )
            group_frame.pack(fill=X, padx=5, pady=5)
            
            # Group info
            total_size = sum(os.path.getsize(f) for f in images if os.path.exists(f))
            info_label = ttk.Label(
                group_frame,
                text=f"{self._format_size(total_size)} - {len(images)} ภาพ"
            )
            info_label.pack(anchor=E, padx=10)
            
            # Thumbnails frame
            thumbs_frame = ttk.Frame(group_frame)
            thumbs_frame.pack(fill=X, padx=5, pady=5)
            
            for img_path in images:
                self._create_category_thumbnail_ui(category, thumbs_frame, img_path, images)
    
    def _create_category_thumbnail_ui(self, category, parent, img_path, group):
        """Create thumbnail with checkbox for an image"""
        manager = self.category_managers[category]
        thumb_frame = ttk.Frame(parent)
        thumb_frame.pack(side=LEFT, padx=5, pady=5)
        
        # Checkbox
        var = tk.BooleanVar(value=False)
        manager['checkboxes'][img_path] = var
        
        cb = ttk.Checkbutton(
            thumb_frame,
            variable=var,
            command=lambda: self._on_category_checkbox_toggle(category, img_path),
            bootstyle="primary-round-toggle"
        )
        cb.pack(anchor=NE)
        
        # Thumbnail image
        try:
            img = imread_unicode(img_path)
            if img is not None:
                thumb = self.resize_image(img, 120, 90)
                thumb_tk = ImageTk.PhotoImage(Image.fromarray(thumb))
                
                thumb_label = ttk.Label(thumb_frame, image=thumb_tk, cursor="hand2")
                thumb_label.image_tk = thumb_tk
                thumb_label.pack()
                
                # Click to preview and set current group
                thumb_label.bind("<Button-1>", lambda e, p=img_path, g=group: self._on_thumbnail_click(category, p, g))
        except Exception as e:
            ttk.Label(thumb_frame, text="[Error]").pack()
        
        # Filename (highlight if it's a copy)
        filename = os.path.basename(img_path)
        is_copy = 'copy' in filename.lower() or self._get_sort_key(img_path)[0] == 1
        display_name = filename[:12] + "..." if len(filename) > 15 else filename
        
        name_label = ttk.Label(thumb_frame, text=display_name, font=("TkDefaultFont", 8))
        if is_copy:
            name_label.config(foreground="#ff6b6b")  # Red for copies
        name_label.pack()
        
        # File size
        try:
            size = os.path.getsize(img_path)
            ttk.Label(thumb_frame, text=self._format_size(size), font=("TkDefaultFont", 8)).pack()
        except:
            pass
    
    def _on_thumbnail_click(self, category, img_path, group):
        """Handle thumbnail click - open fullscreen image viewer"""
        manager = self.category_managers[category]
        
        # For Black/White: use ALL images in the category folder, not just single-image groups
        if category in ('Black', 'White'):
            # Collect all images from all checkboxes (which represent all images)
            all_images = list(manager['checkboxes'].keys())
            all_images.sort()  # Sort for consistent ordering
            manager['current_group'] = all_images
            manager['preview_index'] = all_images.index(img_path) if img_path in all_images else 0
        else:
            # For Duplicate: use the group as before
            manager['current_group'] = group
            manager['preview_index'] = group.index(img_path) if img_path in group else 0
        
        # Also update small preview
        self._show_category_preview(category, img_path)
        
        # Open fullscreen viewer
        self._open_fullscreen_viewer(category)
    
    def _open_fullscreen_viewer(self, category):
        """Open fullscreen image viewer popup"""
        manager = self.category_managers[category]
        group = manager.get('current_group', [])
        
        if not group:
            return
        
        # Dynamic background color based on category
        # Black border images: use light background to see black borders
        # White border images: use dark background to see white borders
        if category == 'Black':
            bg_color = "#d0dce8"  # Light blue-gray - shows black borders clearly
            info_bg = "#a8b8c8"
            text_color = "#1a1a2e"
        elif category == 'White':
            bg_color = "#1a1a2e"  # Dark navy - shows white borders clearly
            info_bg = "#2a2a4e"
            text_color = "#ffffff"
        else:
            bg_color = "#3d5a80"  # Medium blue - neutral for duplicates
            info_bg = "#2d4a70"
            text_color = "#ffffff"
        
        # Create popup window
        viewer = tk.Toplevel(self.root)
        viewer.title(f"Image Viewer [{category}] - คลิกเพื่อดูภาพถัดไป | กด ESC เพื่อปิด")
        viewer.configure(bg=bg_color)
        
        # Make it fullscreen-like (same size as main window)
        viewer.geometry("1680x1050")
        viewer.resizable(True, True)
        
        # Store viewer state
        self._viewer_window = viewer
        self._viewer_category = category
        self._viewer_index = manager.get('preview_index', 0)
        self._viewer_group = group
        self._viewer_bg_color = bg_color  # Store for use in update
        
        # IMPORTANT: Pack info_frame FIRST with side=BOTTOM
        # Then pack canvas to fill remaining space
        self._viewer_info_frame = tk.Frame(viewer, bg=info_bg, height=50)
        self._viewer_info_frame.pack(fill=tk.X, side=tk.BOTTOM)
        self._viewer_info_frame.pack_propagate(False)
        
        self._viewer_info_label = tk.Label(
            self._viewer_info_frame, 
            text="", 
            bg=info_bg, 
            fg=text_color,
            font=("TkDefaultFont", 11)
        )
        self._viewer_info_label.pack(pady=10)
        
        # Use Canvas instead of Label for better background control
        # Pack AFTER info_frame so it fills remaining space
        self._viewer_canvas = tk.Canvas(viewer, bg=bg_color, highlightthickness=0, cursor="hand2")
        self._viewer_canvas.pack(fill=tk.BOTH, expand=True)
        
        # Bind events - click left side for prev, right side for next
        self._viewer_canvas.bind("<Button-1>", self._viewer_on_click)
        viewer.bind("<Right>", lambda e: self._viewer_next_image())
        viewer.bind("<Left>", lambda e: self._viewer_prev_image())
        viewer.bind("<Escape>", lambda e: viewer.destroy())
        viewer.bind("<space>", lambda e: self._viewer_next_image())
        viewer.bind("<Configure>", lambda e: self._update_viewer_image())
        
        # Show first image
        self._update_viewer_image()
        
        # Focus on viewer
        viewer.focus_set()
    
    def _update_viewer_image(self):
        """Update the image in fullscreen viewer"""
        if not hasattr(self, '_viewer_window') or not self._viewer_window.winfo_exists():
            return
        
        if not hasattr(self, '_viewer_canvas'):
            return
        
        group = self._viewer_group
        idx = self._viewer_index
        
        if not group or idx >= len(group):
            return
        
        img_path = group[idx]
        
        try:
            img = imread_unicode(img_path)
            if img is None:
                return
            
            # Get canvas size
            self._viewer_canvas.update_idletasks()
            canvas_width = self._viewer_canvas.winfo_width()
            canvas_height = self._viewer_canvas.winfo_height()
            
            if canvas_width < 10 or canvas_height < 10:
                return  # Canvas not ready
            
            # Resize image to fit canvas while maintaining aspect ratio
            img_height, img_width = img.shape[:2]
            scale = min(canvas_width / img_width, canvas_height / img_height)
            new_width = int(img_width * scale)
            new_height = int(img_height * scale)
            
            resized = cv2.resize(img, (new_width, new_height), interpolation=cv2.INTER_LANCZOS4)
            resized_rgb = cv2.cvtColor(resized, cv2.COLOR_BGR2RGB)
            
            img_tk = ImageTk.PhotoImage(Image.fromarray(resized_rgb))
            
            # Clear canvas and draw background rectangle first
            self._viewer_canvas.delete("all")
            
            # Draw background rectangle to ensure color is visible (workaround for theme issues)
            bg_color = getattr(self, '_viewer_bg_color', '#3d5a80')
            self._viewer_canvas.create_rectangle(0, 0, canvas_width, canvas_height, fill=bg_color, outline=bg_color)
            
            # Calculate center position
            x_center = canvas_width // 2
            y_center = canvas_height // 2
            
            self._viewer_canvas.create_image(x_center, y_center, image=img_tk, anchor=tk.CENTER)
            self._viewer_canvas.image_tk = img_tk  # Keep reference
            
            # Update info
            filename = os.path.basename(img_path)
            size = self._format_size(os.path.getsize(img_path))
            self._viewer_info_label.config(
                text=f"{filename}  |  {img_width}x{img_height}  |  {size}  |  ภาพ {idx + 1}/{len(group)}"
            )
            
            # Also update small preview
            self._show_category_preview(self._viewer_category, img_path)
            
        except Exception as e:
            print(f"Error updating viewer: {e}")
    
    def _viewer_next_image(self):
        """Show next image in viewer"""
        if not hasattr(self, '_viewer_group'):
            return
        
        self._viewer_index = (self._viewer_index + 1) % len(self._viewer_group)
        self._update_viewer_image()
    
    def _viewer_prev_image(self):
        """Show previous image in viewer"""
        if not hasattr(self, '_viewer_group'):
            return
        
        self._viewer_index = (self._viewer_index - 1) % len(self._viewer_group)
        self._update_viewer_image()
    
    def _viewer_on_click(self, event):
        """Handle click on viewer canvas - left half = prev, right half = next"""
        if not hasattr(self, '_viewer_canvas'):
            return
        
        # Get canvas width
        canvas_width = self._viewer_canvas.winfo_width()
        
        # Determine which half was clicked
        if event.x < canvas_width / 2:
            # Left side - previous image
            self._viewer_prev_image()
        else:
            # Right side - next image
            self._viewer_next_image()
    
    def _show_category_preview(self, category, img_path):
        """Show image preview and detailed metadata"""
        try:
            img = imread_unicode(img_path)
            if img is not None:
                preview = self.resize_image(img, 380, 280)
                preview_tk = ImageTk.PhotoImage(Image.fromarray(preview))
                
                self.cat_ui[category]['preview_label'].config(image=preview_tk)
                self.cat_ui[category]['preview_label'].image_tk = preview_tk
            
            # Get file stats
            stat = os.stat(img_path)
            ctime = datetime.datetime.fromtimestamp(stat.st_ctime).strftime('%Y-%m-%d %H:%M:%S')
            mtime = datetime.datetime.fromtimestamp(stat.st_mtime).strftime('%Y-%m-%d %H:%M:%S')
            
            # Get image info using PIL
            pil_img = Image.open(img_path)
            img_width, img_height = pil_img.size
            
            # Calculate aspect ratio
            g = gcd(img_width, img_height)
            ratio_w = img_width // g
            ratio_h = img_height // g
            if ratio_w > 10 or ratio_h > 10:
                aspect_ratio = f"{img_width/img_height:.2f}:1"
            else:
                aspect_ratio = f"{ratio_w}:{ratio_h}"
            
            # Calculate megapixels
            megapixels = (img_width * img_height) / 1000000
            
            # Update all metadata fields
            self.cat_ui[category]['filename_var'].set(os.path.basename(img_path))
            self.cat_ui[category]['path_var'].set(os.path.dirname(img_path))
            self.cat_ui[category]['size_var'].set(self._format_size(stat.st_size))
            self.cat_ui[category]['ctime_var'].set(ctime)
            self.cat_ui[category]['mtime_var'].set(mtime)
            self.cat_ui[category]['dimensions_var'].set(f"{img_width} × {img_height} pixels")
            self.cat_ui[category]['aspect_var'].set(aspect_ratio)
            self.cat_ui[category]['megapixels_var'].set(f"{megapixels:.2f} MP")
            self.cat_ui[category]['mode_var'].set(pil_img.mode)
            self.cat_ui[category]['format_var'].set(pil_img.format or 'Unknown')
            
            pil_img.close()
            
        except Exception as e:
            print(f"Error showing preview: {e}")
    
    def _on_category_checkbox_toggle(self, category, img_path):
        """Handle checkbox toggle"""
        manager = self.category_managers[category]
        var = manager['checkboxes'].get(img_path)
        if var:
            if var.get():
                manager['selected'].add(img_path)
            else:
                manager['selected'].discard(img_path)
        self._update_category_remove_button(category)
    
    def _update_category_remove_button(self, category):
        """Update remove button text with count"""
        manager = self.category_managers[category]
        count = len(manager['selected'])
        total_size = sum(os.path.getsize(f) for f in manager['selected'] if os.path.exists(f))
        
        # Update old UI if exists
        if hasattr(self, 'cat_ui') and category in self.cat_ui and 'remove_btn' in self.cat_ui[category]:
            self.cat_ui[category]['remove_btn'].config(
                text=f"🗑 Remove Selected ({count}) - {self._format_size(total_size)}"
            )
        
        # Update gallery UI if this category is currently shown
        if self.current_gallery_category == category:
            self._update_gallery_remove_button()
            self._update_auto_mark_button()
    
    def auto_mark_category(self, category):
        """Auto mark: keep original, mark copies for deletion"""
        if not self.selected_folder:
            return
        
        manager = self.category_managers[category]
        
        # Clear previous selections
        manager['selected'].clear()
        for var in manager['checkboxes'].values():
            var.set(False)
        
        # Get all files from the category folder
        category_folder = os.path.join(self.selected_folder, category)
        good_folder = os.path.join(self.selected_folder, "Good")
        
        image_extensions = ('.jpg', '.jpeg', '.png', '.tif', '.tiff', '.bmp')
        all_images = []
        
        if os.path.exists(category_folder):
            for f in os.listdir(category_folder):
                if f.lower().endswith(image_extensions):
                    filepath = os.path.join(category_folder, f)
                    if os.path.isfile(filepath):
                        all_images.append(filepath)
        
        if category == 'Duplicate' and os.path.exists(good_folder):
            for f in os.listdir(good_folder):
                if f.lower().endswith(image_extensions):
                    filepath = os.path.join(good_folder, f)
                    if os.path.isfile(filepath):
                        all_images.append(filepath)
        
        if category == 'Duplicate':
            # For Duplicate: mark only files with 'copy' in filename (case insensitive)
            for path in all_images:
                filename = os.path.basename(path).lower()
                # Mark if filename contains 'copy'
                if 'copy' in filename:
                    manager['selected'].add(path)
                    if path in manager['checkboxes']:
                        manager['checkboxes'][path].set(True)
        else:
            # For Black/White: mark only COPY files, keep originals
            for path in all_images:
                # Check if it's a copy file (sort key returns (1, ...) for copies)
                if self._get_sort_key(path)[0] == 1:
                    manager['selected'].add(path)
                    if path in manager['checkboxes']:
                        manager['checkboxes'][path].set(True)
        
        self._update_gallery_remove_button()
        self._update_auto_mark_button()
    
    def unmark_all_category(self, category):
        """Unmark all selected in category"""
        manager = self.category_managers[category]
        manager['selected'].clear()
        for var in manager['checkboxes'].values():
            var.set(False)
        self._update_category_remove_button(category)
    
    def remove_selected_category(self, category):
        """Remove selected files in category"""
        manager = self.category_managers[category]
        
        if not manager['selected']:
            return
        
        count = len(manager['selected'])
        if messagebox.askyesno("ยืนยันการลบ", f"ต้องการลบ {count} ภาพที่เลือกใช่หรือไม่?"):
            deleted = 0
            for path in list(manager['selected']):
                try:
                    os.remove(path)
                    deleted += 1
                except Exception as e:
                    print(f"Error deleting {path}: {e}")
            
            messagebox.showinfo("เสร็จสิ้น", f"ลบไฟล์แล้ว {deleted} ไฟล์")
            self.refresh_category_groups(category)
    
    def _format_size(self, size_bytes):
        """Format file size to human readable"""
        if size_bytes < 1024:
            return f"{size_bytes} B"
        elif size_bytes < 1024 * 1024:
            return f"{size_bytes / 1024:.1f} KB"
        else:
            return f"{size_bytes / (1024 * 1024):.2f} MB"
    
    def split_files_dialog(self, source_folder=None):
        """
        Show dialog to configure and split files into numbered subfolders.
        Uses the provided source_folder or the currently selected folder.
        """
        # Use provided folder or current selected folder
        if source_folder is None:
            source_folder = self.selected_folder
        
        if not source_folder or not os.path.exists(source_folder):
            messagebox.showinfo("ไม่พบโฟลเดอร์", "กรุณาเลือกโฟลเดอร์ก่อน")
            return
        
        # Count image files
        image_extensions = ('.jpg', '.jpeg', '.png', '.tif', '.tiff', '.bmp')
        image_files = [f for f in os.listdir(source_folder) 
                       if f.lower().endswith(image_extensions) 
                       and os.path.isfile(os.path.join(source_folder, f))]
        
        total_files = len(image_files)
        if total_files == 0:
            messagebox.showinfo("ไม่พบไฟล์", "ไม่พบไฟล์รูปภาพในโฟลเดอร์นี้")
            return
        
        # Simple dialog - just ask for files per folder
        dialog = tk.Toplevel(self.root)
        dialog.title("แบ่งไฟล์")
        dialog.geometry("350x200")
        dialog.resizable(False, False)
        dialog.transient(self.root)
        dialog.grab_set()
        
        # File count info
        tk.Label(
            dialog, 
            text=f"พบไฟล์รูปภาพ: {total_files} ไฟล์",
            font=("TkDefaultFont", 12, "bold")
        ).pack(pady=15)
        
        # Max files per folder
        max_frame = tk.Frame(dialog)
        max_frame.pack(fill=tk.X, padx=20, pady=10)
        tk.Label(max_frame, text="จำนวนไฟล์ต่อโฟลเดอร์:", font=("TkDefaultFont", 11)).pack(side=tk.LEFT)
        max_var = tk.StringVar(value="100")
        max_entry = tk.Entry(max_frame, textvariable=max_var, font=("TkDefaultFont", 11), width=8)
        max_entry.pack(side=tk.LEFT, padx=10)
        max_entry.focus_set()
        max_entry.select_range(0, tk.END)
        
        # Prefix (hidden default)
        prefix = "Batch"
        
        # Estimated folders
        estimate_label = tk.Label(dialog, text="", font=("TkDefaultFont", 10))
        estimate_label.pack(pady=5)
        
        def update_estimate(*args):
            try:
                max_per_folder = int(max_var.get())
                if max_per_folder > 0:
                    num_folders = math.ceil(total_files / max_per_folder)
                    estimate_label.config(text=f"จะสร้าง {num_folders} โฟลเดอร์")
                else:
                    estimate_label.config(text="")
            except:
                estimate_label.config(text="")
        
        max_var.trace_add("write", update_estimate)
        update_estimate()
        
        def do_split():
            try:
                max_per_folder = int(max_var.get())
                
                if max_per_folder < 1:
                    messagebox.showerror("ข้อผิดพลาด", "จำนวนไฟล์ต้องมากกว่า 0")
                    return
                
                # Sort files for consistent ordering
                image_files.sort()
                
                # Create subfolders and move files
                folder_num = 1
                file_count = 0
                moved_count = 0
                current_folder = None
                
                for filename in image_files:
                    if file_count >= max_per_folder or current_folder is None:
                        # Create new subfolder
                        current_folder = os.path.join(source_folder, f"{prefix}_{folder_num:03d}")
                        os.makedirs(current_folder, exist_ok=True)
                        folder_num += 1
                        file_count = 0
                    
                    # Move file
                    src_path = os.path.join(source_folder, filename)
                    dest_path = os.path.join(current_folder, filename)
                    
                    try:
                        shutil.move(src_path, dest_path)
                        moved_count += 1
                        file_count += 1
                    except Exception as e:
                        print(f"Error moving {filename}: {e}")
                
                dialog.destroy()
                messagebox.showinfo(
                    "แบ่งไฟล์เสร็จสิ้น", 
                    f"ย้ายไฟล์ {moved_count} ไฟล์\nไปยัง {folder_num - 1} โฟลเดอร์"
                )
                
            except ValueError:
                messagebox.showerror("ข้อผิดพลาด", "กรุณาใส่ตัวเลขที่ถูกต้อง")
        
        # Buttons
        btn_frame = tk.Frame(dialog)
        btn_frame.pack(pady=15)
        
        ttk.Button(
            btn_frame, 
            text="✓ แบ่งไฟล์", 
            command=do_split,
            bootstyle="success"
        ).pack(side=tk.LEFT, padx=10)
        
        ttk.Button(
            btn_frame, 
            text="✗ ยกเลิก", 
            command=dialog.destroy,
            bootstyle="secondary"
        ).pack(side=tk.LEFT, padx=10)
        
        # Bind Enter key
        dialog.bind('<Return>', lambda e: do_split())
        
        # Center dialog
        dialog.update_idletasks()
        x = self.root.winfo_x() + (self.root.winfo_width() - dialog.winfo_width()) // 2
        y = self.root.winfo_y() + (self.root.winfo_height() - dialog.winfo_height()) // 2
        dialog.geometry(f"+{x}+{y}")
    
    # ==================== METADATA REMOVAL ====================
    
    def remove_metadata_from_file(self, filepath):
        """
        Remove metadata from image file (in-place).
        Based on MetaSweep Pro's approach.
        """
        filepath_lower = filepath.lower()
        
        try:
            if filepath_lower.endswith(('.jpg', '.jpeg')):
                self._remove_jpeg_metadata(filepath)
            elif filepath_lower.endswith('.png'):
                self._remove_png_metadata(filepath)
            # Other formats (tif, bmp) are left as-is for now
        except Exception as e:
            print(f"Error removing metadata from {filepath}: {e}")
    
    def _remove_jpeg_metadata(self, filepath):
        """
        Remove all metadata markers from JPEG for complete clean sweep.
        
        Markers removed:
        - 0xE1 (APP1): EXIF, XMP
        - 0xE2 (APP2): ICC Profile  
        - 0xEB (APP11): JUMBF, C2PA, Google Generative AI
        - 0xEC (APP12): Picture Info
        - 0xED (APP13): IPTC, Photoshop Resources
        - 0xEE (APP14): Adobe
        - 0xFE (COM): JPEG Comments
        """
        with open(filepath, 'rb') as f:
            data = f.read()
            
        # Verify JPEG
        if data[:2] != b'\xff\xd8':
            return  # Not a valid JPEG
            
        # Build new file without metadata segments
        new_data = bytearray()
        new_data.extend(data[:2])  # SOI marker
        
        # Markers to REMOVE for complete clean sweep
        markers_to_remove = {
            0xE1,  # APP1 - EXIF/XMP
            0xE2,  # APP2 - ICC Profile
            0xEB,  # APP11 - JUMBF/C2PA/Google AI
            0xEC,  # APP12 - Picture Info
            0xED,  # APP13 - IPTC/Photoshop
            0xEE,  # APP14 - Adobe
            0xFE,  # COM - Comments
        }
        
        i = 2
        while i < len(data) - 1:
            if data[i] != 0xff:
                new_data.extend(data[i:])
                break
                
            marker = data[i + 1]
            
            # SOS - Start of Scan (image data begins)
            if marker == 0xda:
                new_data.extend(data[i:])
                break
                
            # EOI - End of Image
            if marker == 0xd9:
                new_data.extend(data[i:i+2])
                break
                
            # Markers without length (RST0-RST7, SOI, EOI, TEM)
            if marker in (0xd0, 0xd1, 0xd2, 0xd3, 0xd4, 0xd5, 0xd6, 0xd7, 0xd8, 0xd9, 0x01):
                new_data.extend(data[i:i+2])
                i += 2
                continue
                
            # Get segment length
            if i + 3 >= len(data):
                break
            length = (data[i + 2] << 8) + data[i + 3]
            
            # Check if marker should be removed
            if marker in markers_to_remove:
                # Skip this segment (don't copy)
                i += 2 + length
            else:
                # Keep this segment
                new_data.extend(data[i:i + 2 + length])
                i += 2 + length
                
        # Write back to file
        with open(filepath, 'wb') as f:
            f.write(new_data)
    
    def _remove_png_metadata(self, filepath):
        """Remove metadata chunks from PNG, keep only essential chunks."""
        with open(filepath, 'rb') as f:
            data = f.read()
            
        png_signature = b'\x89PNG\r\n\x1a\n'
        if data[:8] != png_signature:
            return  # Not a valid PNG
            
        # Chunks to keep (essential for image display)
        keep_chunks = {b'IHDR', b'PLTE', b'IDAT', b'IEND', b'tRNS', b'cHRM',
                       b'gAMA', b'sBIT', b'bKGD', b'hIST', b'pHYs', b'sPLT'}
                       
        new_data = bytearray()
        new_data.extend(png_signature)
        
        i = 8
        while i < len(data):
            if i + 8 > len(data):
                break
                
            length = int.from_bytes(data[i:i+4], 'big')
            chunk_type = data[i+4:i+8]
            chunk_size = 12 + length
            
            if i + chunk_size > len(data):
                break
                
            # Keep only essential chunks
            if chunk_type in keep_chunks:
                new_data.extend(data[i:i + chunk_size])
                
            i += chunk_size
            
        with open(filepath, 'wb') as f:
            f.write(new_data)
    
    def select_folder(self):
        """Select folder containing images"""
        folder = filedialog.askdirectory(title="Select folder with images")
        if not folder:
            return  # User cancelled
        
        # Clear previous data first (but keep selected_folder for now)
        old_folder = self.selected_folder
        self._thumbnail_cache = {}
        if hasattr(self, '_hash_cache'):
            self._hash_cache = {}
        self.image_hashes = {}
        
        # Hide gallery if shown
        if self.current_gallery_category:
            self.hide_category_gallery()
        
        # Reset category managers
        for cat in self.category_managers:
            self.category_managers[cat] = {
                'groups': {}, 'selected': set(), 'checkboxes': {}, 
                'current_group': [], 'preview_index': 0
            }
        
        # Clear category previews
        for cat_name in self.categories.values():
            if cat_name in self.category_labels:
                self.category_labels[cat_name].config(image='')
        
        # Clear image displays
        self.left_img_label.config(image='')
        self.right_img_label.config(image='')
        
        self.selected_folder = folder
        
        # Update select button text to show folder name
        folder_name = os.path.basename(folder)
        self.select_btn.config(text=f"📂 {folder_name}")
        
        # Create output folders
        for category in self.categories.values():
            category_folder = os.path.join(folder, category)
            os.makedirs(category_folder, exist_ok=True)
        
        # Update category counts
        self.update_category_counts()
        
        # Get all image files
        image_extensions = ('.jpg', '.jpeg', '.png', '.tif', '.tiff', '.bmp')
        image_files = [
            os.path.join(folder, f) for f in os.listdir(folder)
            if f.lower().endswith(image_extensions) and os.path.isfile(os.path.join(folder, f))
        ]
        
        # If no images found, just update UI without error popup
        if not image_files:
            self.progress_label.config(text="No images found in this folder")
            self.progress_bar["value"] = 0
            self.progress_bar["maximum"] = 0
            return
        
        # Clear existing queues
        while not self.left_queue.empty():
            self.left_queue.get()
        while not self.right_queue.empty():
            self.right_queue.get()
        
        # Reset processing state
        self.total_images = len(image_files)
        self.processed_images = 0
        
        # Split images between queues (50% each)
        middle_index = math.ceil(self.total_images / 2)
        
        # First half to left queue
        for i in range(0, middle_index):
            self.left_queue.put(image_files[i])
        
        # Second half to right queue
        for i in range(middle_index, self.total_images):
            self.right_queue.put(image_files[i])
        
        # Update UI
        self.progress_label.config(text=f"Ready to process {self.total_images} images")
        self.progress_bar["value"] = 0
        self.progress_bar["maximum"] = self.total_images
        self.start_btn.config(state=NORMAL)
        self.timer_label.config(text="Time: 00:00:00")
    
    def toggle_processing(self):
        """Start or stop image processing"""
        if self.processing:
            # Stop processing
            self.processing = False
            self.start_btn.config(text="Start Processing", bootstyle="success")
            self.stop_timer()
        else:
            # Check if we have images to process
            if self.left_queue.empty() and self.right_queue.empty():
                messagebox.showinfo("No Images", "Please select a folder with images first.")
                return
            
            # Start processing
            self.processing = True
            self.start_btn.config(text="Stop Processing", bootstyle="danger")
            
            # Start the timer
            self.start_timer()
            
            # Launch processing threads
            threading.Thread(target=self.process_left_images, daemon=True).start()
            threading.Thread(target=self.process_right_images, daemon=True).start()
    
    def start_timer(self):
        """Start the processing timer"""
        self.start_time = time.time()
        self.update_timer()
    
    def stop_timer(self):
        """Stop the timer"""
        self.start_time = None
    
    def update_timer(self):
        """Update the timer display"""
        if self.start_time and self.processing:
            elapsed = time.time() - self.start_time
            hours = int(elapsed // 3600)
            minutes = int((elapsed % 3600) // 60)
            seconds = int(elapsed % 60)
            
            time_str = f"Time: {hours:02d}:{minutes:02d}:{seconds:02d}"
            self.timer_label.config(text=time_str)
            
            # Schedule the next update
            self.root.after(1000, self.update_timer)
    
    def process_left_images(self):
        """Process images from the left queue"""
        self.process_images(self.left_queue, 0)
    
    def process_right_images(self):
        """Process images from the right queue"""
        self.process_images(self.right_queue, 1)
    
    def process_images(self, image_queue, position):
        """Process images from a queue using multi-core processing"""
        if not self.executor:
            self.executor = ProcessPoolExecutor(max_workers=self.num_cores)

        while self.processing and not image_queue.empty():
            try:
                # Get next image
                image_path = image_queue.get(block=False)
                
                # Copy hashes with lock to ensure thread-safety
                # This prevents race condition where duplicate images are missed
                with self.hash_lock:
                    current_hashes = self.image_hashes.copy()
                
                # Check image using process pool
                future = self.executor.submit(
                    check_image_standalone, 
                    image_path, 
                    position, 
                    current_hashes
                )
                
                # Wait for result
                result = future.result()
                
                if result.get('error'):
                    image_queue.task_done()
                    continue

                # Update hash IMMEDIATELY after getting result (before anything else)
                # This ensures the next image check will see this hash
                if result.get('new_hashes'):
                    with self.hash_lock:
                        self.image_hashes.update(result['new_hashes'])

                # Load image for display (this is done in main thread to avoid pickling issues)
                img = imread_unicode(image_path)
                if img is None:
                    image_queue.task_done()
                    continue
                
                # Display image
                self.update_image_display(img, position)

                # Put result in result queue
                self.result_queue.put(result)
                
                # Update progress
                self.processed_images += 1
                self.root.after(0, self.update_progress)
                
                # Mark task done
                image_queue.task_done()
                
                # Reduced delay
                time.sleep(0.01)
                
            except queue.Empty:
                break
            except Exception as e:
                print(f"Error processing image: {e}")
                image_queue.task_done()
        
        # If all queues empty, finalize
        if (self.left_queue.empty() and self.right_queue.empty() and self.processing):
            self.root.after(0, self.finalize_processing)
    
    def update_image_display(self, img, position):
        """Display image in the appropriate panel"""
        if position == 0:
            label = self.left_img_label
            # ปรับขนาดให้เหมาะสมกับหน้าจอที่เล็กลง
            width = 800
            height = 450
        else:
            label = self.right_img_label
            # ปรับขนาดให้เหมาะสมกับหน้าจอที่เล็กลง
            width = 800
            height = 450
        
        # Resize image to fit panel
        display_img = self.resize_image(img, width, height)
        
        # Convert to tkinter format
        img_tk = ImageTk.PhotoImage(Image.fromarray(display_img))
        
        # Update label
        self.root.after(0, lambda: label.configure(image=img_tk))
        self.root.after(0, lambda: setattr(label, 'image_tk', img_tk))
    
    def resize_image(self, img, width, height):
        """Resize image to fit dimensions while preserving aspect ratio"""
        h, w = img.shape[:2]
        
        # Calculate scale to fit
        scale_w = width / w
        scale_h = height / h
        scale = min(scale_w, scale_h)
        
        # New dimensions
        new_w = int(w * scale)
        new_h = int(h * scale)
        
        # Resize image
        resized = cv2.resize(img, (new_w, new_h))
        
        # Create background canvas
        canvas = np.zeros((height, width, 3), dtype=np.uint8)
        
        # Center image on canvas
        x_offset = (width - new_w) // 2
        y_offset = (height - new_h) // 2
        
        # Place image
        canvas[y_offset:y_offset+new_h, x_offset:x_offset+new_w] = resized
        
        # Convert to RGB
        return cv2.cvtColor(canvas, cv2.COLOR_BGR2RGB)
    
    def update_progress(self):
        """Update progress indicators"""
        self.progress_bar["value"] = self.processed_images
        self.progress_label.config(
            text=f"Processed {self.processed_images} of {self.total_images} images"
        )
    
    def finalize_processing(self):
        """Reset processing state when complete"""
        self.processing = False
        self.start_btn.config(text="Start Processing", bootstyle="success")
        self.stop_timer()
        
        # Update category counts
        self.update_category_counts()
        
        # Record end time and display total duration
        if self.start_time:
            elapsed = time.time() - self.start_time
            hours = int(elapsed // 3600)
            minutes = int((elapsed % 3600) // 60)
            seconds = int(elapsed % 60)
            
            end_time_str = f"Total Time: {hours:02d}:{minutes:02d}:{seconds:02d}"
            self.timer_label.config(text=end_time_str)
            
            # Show completion message
            messagebox.showinfo(
                "Processing Complete", 
                f"Processed {self.processed_images} images in {end_time_str}"
            )
    
    def process_results(self):
        """Handle results from the result queue"""
        while True:
            try:
                # Get result
                result = self.result_queue.get()
                
                # Skip errors
                if result.get('error'):
                    self.result_queue.task_done()
                    continue
                
                # Get category and path
                category_id = result['category']
                category_name = self.categories[category_id]
                image_path = result['path']
                
                # Create destination path
                if self.selected_folder:
                    dest_folder = os.path.join(self.selected_folder, category_name)
                    dest_path = os.path.join(dest_folder, os.path.basename(image_path))
                    
                    try:
                        # Make a copy of the image before moving (for display)
                        img = imread_unicode(image_path)
                        
                        # Move file to appropriate folder
                        shutil.move(image_path, dest_path)
                        
                        # Remove metadata from the moved file (in-place)
                        self.remove_metadata_from_file(dest_path)
                        
                        # Store the moved image path for the category
                        self.last_processed[category_name] = dest_path
                        
                        # Update thumbnail with the moved image
                        if img is not None:
                            self.update_category_thumbnail(category_name, img)
                    except Exception as e:
                        print(f"Error moving file: {e}")
                
                # Mark task complete
                self.result_queue.task_done()
                
            except Exception as e:
                print(f"Error processing result: {e}")
                time.sleep(0.1)
    
    def update_category_thumbnail(self, category_name, img):
        """Update thumbnail in category panel"""
        if category_name not in self.category_labels:
            return
        
        # ปรับขนาด thumbnail ให้เข้ากับหน้าจอที่เล็กลง
        width = 400  # ปรับตามความเหมาะสม
        height = 200  # ปรับตามความเหมาะสม
        
        # Resize for display
        thumb = self.resize_image(img, width, height)
        
        # Convert to tkinter format
        thumb_tk = ImageTk.PhotoImage(Image.fromarray(thumb))
        
        # Update label
        label = self.category_labels[category_name]
        self.root.after(0, lambda: label.configure(image=thumb_tk))
        self.root.after(0, lambda: setattr(label, 'image_tk', thumb_tk))
        
        # Update category count
        self.root.after(0, self.update_category_counts)
    
def prepare_image(image_path):
    """
    Load image and handle PNG transparency by compositing onto a white background.
    Also handles grayscale images by converting to BGR.
    Returns: tuple (BGR image (numpy array), has_transparency (bool))
    """
    img = imread_unicode(image_path, cv2.IMREAD_UNCHANGED)
    if img is None:
        return None, False
    
    # Handle different channel counts
    if len(img.shape) == 2:
        # Grayscale image (1 channel) - convert to BGR
        return cv2.cvtColor(img, cv2.COLOR_GRAY2BGR), False
    
    if img.shape[2] == 1:
        # Single channel image - convert to BGR
        return cv2.cvtColor(img, cv2.COLOR_GRAY2BGR), False
    
    if img.shape[2] == 2:
        # Grayscale with alpha - composite onto white then convert
        gray = img[:, :, 0]
        alpha = img[:, :, 1] / 255.0
        # Check if there's actual transparency (not all fully opaque)
        has_transparency = np.any(alpha < 0.99)
        background = np.ones(gray.shape, dtype=np.uint8) * 255
        composited = (alpha * gray + (1 - alpha) * background).astype(np.uint8)
        return cv2.cvtColor(composited, cv2.COLOR_GRAY2BGR), has_transparency
    
    if img.shape[2] == 4:
        # BGRA image - composite onto white background
        alpha = img[:, :, 3] / 255.0
        # Check if there's actual transparency (not all fully opaque)
        has_transparency = np.any(alpha < 0.99)
        background = np.ones((img.shape[0], img.shape[1], 3), dtype=np.uint8) * 255
        for c in range(0, 3):
            background[:, :, c] = (alpha * img[:, :, c] + (1 - alpha) * background[:, :, c]).astype(np.uint8)
        return background, has_transparency
    
    # If it's already 3 channels (BGR)
    return img, False


def check_duplicate_standalone(img, image_path, existing_hashes):
    """
    Check if image is a duplicate using perceptual hash.
    Based on PhotoSweep's approach with imagehash.hex_to_hash() for proper Hamming distance.
    
    Args:
        img: BGR image (numpy array)
        image_path: path to current image
        existing_hashes: dict of {path: hash_string}
    
    Returns:
        tuple (is_duplicate: bool, hash_string: str)
    """
    # Convert to PIL for hashing
    pil_img = Image.fromarray(cv2.cvtColor(img, cv2.COLOR_BGR2RGB))
    
    # Resize large images to avoid MemoryError (PhotoSweep approach)
    max_dim = 2048
    if pil_img.width > max_dim or pil_img.height > max_dim:
        ratio = min(max_dim / pil_img.width, max_dim / pil_img.height)
        new_size = (int(pil_img.width * ratio), int(pil_img.height * ratio))
        pil_img = pil_img.resize(new_size, Image.LANCZOS)
    
    # Convert to RGB if needed
    if pil_img.mode != 'RGB':
        pil_img = pil_img.convert('RGB')
    
    # Calculate perceptual hash with larger hash_size for more accuracy
    current_hash = imagehash.phash(pil_img, hash_size=HASH_SIZE)
    current_hash_str = str(current_hash)
    
    # Compare with existing hashes using proper Hamming distance
    for path, stored_hash_str in existing_hashes.items():
        if path == image_path:
            continue
        
        try:
            # Use imagehash.hex_to_hash for proper comparison (PhotoSweep method)
            stored_hash = imagehash.hex_to_hash(stored_hash_str)
            distance = current_hash - stored_hash  # Hamming distance
            
            if distance <= SIMILARITY_THRESHOLD:
                return True, current_hash_str
        except Exception:
            # If hash comparison fails, skip this comparison
            pass
    
    return False, current_hash_str

def check_image_standalone(image_path, position, existing_hashes):
    """
    Standalone function to be run in a separate process.
    """
    try:
        # 1. Prepare image (handle transparency)
        img, has_transparency = prepare_image(image_path)
        if img is None:
            return {'error': True, 'path': image_path}
            
        result = {
            'filename': os.path.basename(image_path),
            'path': image_path,
            'position': position,
            'is_good': True,
            'category': 'good',
            'error': False,
            'new_hashes': {}
        }
        
        # 2. Check for duplicates
        is_duplicate, hashes = check_duplicate_standalone(img, image_path, existing_hashes)
        result['new_hashes'] = {image_path: hashes}
        
        if is_duplicate:
            result['is_good'] = False
            result['category'] = 'duplicate'
            return result
            
        # 3. Check for borders using standalone function
        # Skip border detection for transparent PNGs as the transparent area 
        # becomes white after compositing and would be wrongly detected as white border
        if not has_transparency:
            border_type = detect_border_standalone(img)
            if border_type:
                result['is_good'] = False
                result['category'] = border_type
                return result
            
        return result
        
    except Exception as e:
        return {'error': True, 'path': image_path, 'exception': str(e)}

def detect_border_standalone(img):
    """
    Standalone version of detect_border_type logic.
    Optimized for execution in separate processes.
    """
    # Convert to grayscale
    gray = cv2.cvtColor(img, cv2.COLOR_BGR2GRAY)
    height, width = gray.shape
    
    # Calculate border margins (5% of image)
    margin_h = max(int(height * 0.05), 10)
    margin_w = max(int(width * 0.05), 10)
    
    # Extract border regions
    top = gray[:margin_h, :]
    bottom = gray[-margin_h:, :]
    left = gray[:, :margin_w]
    right = gray[:, -margin_w:]
    
    # Extract interior region (everything except borders)
    interior = gray[margin_h:height-margin_h, margin_w:width-margin_w]
    
    # Calculate means and stds
    border_regions = [top, bottom, left, right]
    border_means = [np.mean(region) for region in border_regions]
    interior_mean = np.mean(interior)
    border_stds = [np.std(region) for region in border_regions]
    
    # Thresholds
    black_threshold = 15
    white_threshold = 245
    std_threshold = 8
    edge_threshold = 0.1
    
    # 1. Check for Black Borders
    top_black_pct = np.sum(top <= black_threshold) / top.size
    bottom_black_pct = np.sum(bottom <= black_threshold) / bottom.size
    left_black_pct = np.sum(left <= black_threshold) / left.size
    right_black_pct = np.sum(right <= black_threshold) / right.size
    
    is_black = False
    if (top_black_pct > 0.95 and bottom_black_pct > 0.95 and border_stds[0] < std_threshold and border_stds[1] < std_threshold):
        is_black = True
    elif (left_black_pct > 0.95 and right_black_pct > 0.95 and border_stds[2] < std_threshold and border_stds[3] < std_threshold):
        is_black = True
        
    if is_black and abs(interior_mean - np.mean(border_means)) > 40:
        return 'black'
        
    # 2. Check for White Borders
    top_white_pct = np.sum(top >= white_threshold) / top.size
    bottom_white_pct = np.sum(bottom >= white_threshold) / bottom.size
    left_white_pct = np.sum(left >= white_threshold) / left.size
    right_white_pct = np.sum(right >= white_threshold) / right.size
    
    # Check if interior is also very white (e.g., sticker on white background)
    # If interior is mostly white, it's NOT a white border issue
    interior_white_pct = np.sum(interior >= white_threshold) / interior.size
    
    is_white = False
    if (top_white_pct > 0.95 and bottom_white_pct > 0.95 and border_stds[0] < std_threshold and border_stds[1] < std_threshold):
        is_white = True
    elif (left_white_pct > 0.95 and right_white_pct > 0.95 and border_stds[2] < std_threshold and border_stds[3] < std_threshold):
        is_white = True
    
    # Additional check: if interior is also very white (>50%), skip white border detection
    # This prevents false positives for stickers, logos on white backgrounds
    if interior_white_pct > 0.50:
        is_white = False
        
    if is_white and abs(interior_mean - np.mean(border_means)) > 40:
        return 'white'
        
    return None
if __name__ == "__main__":
    # Required for multiprocessing support in compiled (.exe) Windows apps
    multiprocessing.freeze_support()
    
    # Create main window
    root = ttk.Window(themename="darkly")
    
    # สร้างแอปพลิเคชัน
    app = AdobeStockChecker(root)
    
    # แสดงหน้าต่าง
    root.mainloop()

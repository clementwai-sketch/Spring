#!/usr/bin/env python3
import yfinance as yf
import pandas as pd
import numpy as np
import requests
import traceback
from datetime import datetime, timedelta
from rich.table import Table
from rich.console import Console
from rich.progress import Progress, SpinnerColumn, TextColumn
from concurrent.futures import ThreadPoolExecutor, as_completed
import json
from pathlib import Path
import warnings
import threading
from io import StringIO
import sys
from openpyxl.styles import PatternFill, Font, Alignment
import pickle
import hashlib
import hmac
import os
import time
warnings.filterwarnings('ignore')

# Cross-platform file locking (Windows vs Unix/Linux/macOS)
if sys.platform == 'win32':
    import msvcrt
    HAS_FCNTL = False
else:
    import fcntl
    HAS_FCNTL = True

# No external dependencies for swing detection (Zig Zag algorithm built-in)

# Try to import baostock for China A-share fallback
try:
    import baostock as bs
    HAS_BAOSTOCK = True
except ImportError:
    HAS_BAOSTOCK = False

console = Console()

# Thread lock for baostock (API is not thread-safe)
baostock_lock = threading.Lock()

# ============================================================================
# CONFIGURATION
# ============================================================================
# VCP Detection Settings
MIN_CONTRACTIONS = 3          # Minimum 3 progressive waves (Minervini standard: 3-4)
MAX_CONTRACTIONS = 6
CONTRACTION_RATIO = 0.70      # Each pullback must be ≤70% of previous (closer to "half")
CONTRACTION_NOISE_TOLERANCE = 1  # Allow 1 wave slightly exceeding ratio (real VCPs have noise)
CONTRACTION_NOISE_SLACK = 0.15   # Extra tolerance for noise waves (ratio + 15%)
MIN_SWING_DEPTH_PCT = 1.5    # Minimum contraction depth % to count (filters micro-oscillations)
ZIGZAG_PCT = 5.0             # Default Zig Zag reversal threshold % (US mid-large cap)
ZIGZAG_PCT_MAP = {            # Per-market thresholds (auto-selected by ticker suffix)
    '.SS': 7.0,               # China A-shares: heavy retail noise + policy swings
    '.SZ': 7.0,               # China A-shares (Shenzhen)
    '.HK': 6.0,               # Hong Kong: wider intraday ranges, ADR arb volatility
    '.T':  4.0,               # Japan: lower-volatility large-caps, clean structure
}
LOOKBACK_PERIOD = 100
MAX_LAST_CONTRACTION = 12.0   # Final contraction must be tight (≤12% depth)
MIN_OVERALL_NARROWING = 2.0   # First contraction must be ≥2x the last (overall narrowing)

# Trend Filter
TREND_MA_PERIOD = 50
MIN_PRICE_ABOVE_MA = 3.0     # Must be 3%+ above 50MA (VCP = continuation in uptrend)

# Volume Settings
VOLUME_MA_PERIOD = 50
REQUIRE_DECREASING_VOLUME = True

# Breakout Settings
PIVOT_LOOKBACK = 20
BREAKOUT_VOLUME_MULTIPLIER = 1.5
SUSTAINED_VOLUME_MULTIPLIER = 1.2  # 3-day avg must exceed 1.2x MA for "sustained" breakout volume
BREAKOUT_LOOKBACK_DAYS = 7    # Check last 7 days for breakout (was 3)

# Relative Strength (Minervini: leaders outperform the market)
RS_BENCHMARK = "RSP"          # Default benchmark for relative strength
RS_BENCHMARK_MAP = {           # Per-market benchmarks (auto-selected by ticker suffix)
    '.HK': '^HSI',             # Hang Seng for Hong Kong stocks
    '.T':  '^N225',            # Nikkei 225 for Japan stocks
    '.SS': 'FXI',              # iShares China Large-Cap ETF (^SSEC unavailable on yfinance)
    '.SZ': 'FXI',              # iShares China Large-Cap ETF for Shenzhen
}
RS_PERIOD = 63                # ~3 months (quarterly) for RS calculation
RS_PERIOD_LONG = 126          # ~6 months for longer-term RS (optional display)

# Liquidity Filters (skip illiquid/penny stocks)
MIN_AVG_VOLUME = 500_000     # Minimum 500k avg daily volume
MIN_PRICE = 5.0              # Minimum stock price ($5 - skip penny stocks)
LIQUIDITY_FILTER_ENABLED = True  # Set False to scan all tickers

# Performance
MAX_WORKERS = 10
HISTORY_PERIOD = "6mo"

# Cache Configuration (6-hour expiry, multi-script safe)
CACHE_ENABLED = True
CACHE_EXPIRY_HOURS = 6
SCRIPT_DIR = Path(__file__).parent  # Script directory (portable, no hardcoded paths)
CACHE_DIR = SCRIPT_DIR / 'cache'  # Relative path: cache/
CACHE_FILE = CACHE_DIR / 'vcp_scanner_cache.pkl'
CACHE_LOCK_FILE = CACHE_DIR / '.cache_lock'  # File lock for multi-script safety
CACHE_VERSION = 1  # Increment if cache format changes (detects incompatible caches)
CACHE_SIG_FILE = CACHE_FILE.with_suffix('.pkl.sig')  # HMAC signature for cache integrity
MAX_LOG_ENTRIES = 5000  # Cap master Excel log rows to prevent unbounded growth

# Create cache directory if it doesn't exist
if CACHE_ENABLED:
    CACHE_DIR.mkdir(parents=True, exist_ok=True)

# ============================================================================
# CACHE UTILITIES (Multi-script safe with file locking - cross-platform)
# ============================================================================
def _acquire_cache_lock(timeout=5):
    """Acquire file lock for safe multi-script cache access (cross-platform)."""
    try:
        lock_file = open(CACHE_LOCK_FILE, 'w')
        start_time = time.time()
        
        if HAS_FCNTL:
            # Unix/Linux/macOS: use fcntl
            while time.time() - start_time < timeout:
                try:
                    fcntl.flock(lock_file.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
                    return lock_file
                except IOError:
                    time.sleep(0.1)
        else:
            # Windows: use msvcrt
            while time.time() - start_time < timeout:
                try:
                    msvcrt.locking(lock_file.fileno(), msvcrt.LK_NBLCK, 1)
                    return lock_file
                except OSError:
                    time.sleep(0.1)
        return None
    except Exception:
        return None

def _release_cache_lock(lock_file):
    """Release file lock (cross-platform)."""
    if lock_file:
        try:
            if HAS_FCNTL:
                # Unix/Linux/macOS
                fcntl.flock(lock_file.fileno(), fcntl.LOCK_UN)
            else:
                # Windows
                msvcrt.locking(lock_file.fileno(), msvcrt.LK_UNLCK, 1)
            lock_file.close()
        except Exception:
            pass

def _get_cache_key():
    """Derive machine-specific key for cache integrity (prevents RCE via pickle tampering)."""
    try:
        uid = str(os.getuid()) if hasattr(os, 'getuid') else os.getenv('USERNAME', 'default')
    except Exception:
        uid = 'default'
    key_material = f"{Path(__file__).resolve()}:{uid}"
    return hashlib.sha256(key_material.encode()).digest()

def _verify_cache_integrity():
    """Verify cache HMAC before deserializing (mitigates pickle RCE attacks)."""
    if not CACHE_SIG_FILE.exists():
        return False
    try:
        with open(CACHE_FILE, 'rb') as f:
            data = f.read()
        with open(CACHE_SIG_FILE, 'r') as f:
            stored_sig = f.read().strip()
        expected_sig = hmac.new(_get_cache_key(), data, hashlib.sha256).hexdigest()
        return hmac.compare_digest(stored_sig, expected_sig)
    except Exception:
        return False

def _sign_cache_file():
    """Write HMAC signature after cache save (integrity seal)."""
    try:
        with open(CACHE_FILE, 'rb') as f:
            data = f.read()
        sig = hmac.new(_get_cache_key(), data, hashlib.sha256).hexdigest()
        with open(CACHE_SIG_FILE, 'w') as f:
            f.write(sig)
    except Exception:
        pass

def is_cache_valid():
    """Check if cache exists and is fresh (not expired)."""
    if not CACHE_ENABLED or not CACHE_FILE.exists():
        return False
    
    # Check expiry
    cache_age_hours = (time.time() - os.path.getmtime(CACHE_FILE)) / 3600
    if cache_age_hours >= CACHE_EXPIRY_HOURS:
        return False
    
    # Verify HMAC integrity before deserializing (security: prevents pickle RCE)
    if not _verify_cache_integrity():
        console.print("[yellow]\u26a0\ufe0f  Cache integrity check failed \u2014 rebuilding (unsigned or tampered)[/yellow]")
        return False
    
    # Check version compatibility (acquire lock to avoid reading partial writes)
    lock_file = _acquire_cache_lock(timeout=3)
    try:
        with open(CACHE_FILE, 'rb') as f:
            cache_data = pickle.load(f)
            # If cache is a dict with 'version' key, validate it
            if isinstance(cache_data, dict) and '__metadata__' in cache_data:
                if cache_data['__metadata__'].get('version') != CACHE_VERSION:
                    console.print(f"[dim]Cache version mismatch (found v{cache_data['__metadata__'].get('version')}, need v{CACHE_VERSION}) - rebuilding[/dim]")
                    return False
    except Exception:
        return False
    finally:
        _release_cache_lock(lock_file)
    
    return True

def load_cache():
    """Load cached ticker data (thread-safe, HMAC-verified)."""
    if not CACHE_ENABLED or not CACHE_FILE.exists():
        return {}
    
    # Security: verify HMAC before pickle.load to prevent RCE from tampered cache
    if not _verify_cache_integrity():
        console.print("[yellow]\u26a0\ufe0f  Cache signature invalid \u2014 ignoring cached data[/yellow]")
        return {}
    
    lock_file = _acquire_cache_lock(timeout=3)
    try:
        with open(CACHE_FILE, 'rb') as f:
            cache_data = pickle.load(f)
            # Extract just the ticker data (exclude metadata)
            if isinstance(cache_data, dict) and '__metadata__' in cache_data:
                # New format with metadata
                ticker_cache = {k: v for k, v in cache_data.items() if k != '__metadata__'}
                return ticker_cache
            else:
                # Old format (direct ticker data)
                return cache_data if cache_data else {}
    except Exception as e:
        console.print(f"[dim]Cache load warning: {e}[/dim]")
        return {}
    finally:
        _release_cache_lock(lock_file)

def save_cache(data):
    """Save ticker data to cache (thread-safe multi-script access)."""
    if not CACHE_ENABLED or not data:
        return
    
    lock_file = _acquire_cache_lock(timeout=3)
    if not lock_file:
        console.print(f"[dim]Could not acquire cache lock - skipping save[/dim]")
        return
    
    try:
        # Add metadata to cache
        cache_data = dict(data)  # Copy ticker data
        cache_data['__metadata__'] = {
            'version': CACHE_VERSION,
            'created': datetime.now().isoformat(),
            'script': Path(__file__).name,
            'ticker_count': len(data)
        }
        
        # Write to temporary file first, then rename (atomic operation)
        temp_file = CACHE_FILE.with_suffix('.pkl.tmp')
        with open(temp_file, 'wb') as f:
            pickle.dump(cache_data, f)
        
        # Atomic rename
        temp_file.replace(CACHE_FILE)
        # Sign the cache file (HMAC integrity seal)
        _sign_cache_file()
        console.print(f"[dim]✓ Cache saved ({len(data)} tickers, v{CACHE_VERSION})[/dim]")
    except Exception as e:
        console.print(f"[dim]Cache save warning: {e}[/dim]")
    finally:
        _release_cache_lock(lock_file)

# ============================================================================
# DATA FETCHING UTILITIES
# ============================================================================
def fetch_china_stock_baostock(ticker, period_days=180):
    """Fetch China A-share data using baostock (thread-safe with lock)
    
    Args:
        ticker: Ticker in format like '930903.SS' or '000001.SZ'
        period_days: Historical period to fetch (default 180 days)
    
    Returns:
        pd.DataFrame with columns [Open, High, Low, Close, Volume] or None if failed
    """
    if not HAS_BAOSTOCK:
        return None
    
    # Use lock to serialize baostock requests (API is not thread-safe)
    with baostock_lock:
        try:
            # Remove .SS/.SZ suffix and convert to baostock format
            code = ticker.replace('.SS', '').replace('.SZ', '')
            
            # Determine exchange: Shanghai (6xxxxx) or Shenzhen (0xxxxx, 2xxxxx, 3xxxxx)
            if code.startswith('6'):
                bao_code = f"sh.{code}"
            else:
                bao_code = f"sz.{code}"
            
            # Calculate date range
            end_date = datetime.now().strftime("%Y-%m-%d")
            start_date = (datetime.now() - timedelta(days=period_days + 30)).strftime("%Y-%m-%d")
            
            # Suppress stderr during baostock calls
            old_stderr = sys.stderr
            sys.stderr = StringIO()
            
            try:
                # Login
                lg = bs.login()
                if lg.error_code != '0':
                    return None
                
                # Query historical data with forward-adjusted prices (adjustflag=2)
                rs = bs.query_history_k_data_plus(
                    bao_code,
                    "date,code,open,high,low,close,volume",
                    start_date=start_date,
                    end_date=end_date,
                    frequency="d",
                    adjustflag="2"
                )
                
                # Collect data
                data_list = []
                if rs.error_code == '0':
                    while rs.next():
                        data_list.append(rs.get_row_data())
                
                bs.logout()
                
                if not data_list:
                    return None
                
                # Create DataFrame
                df = pd.DataFrame(data_list, columns=rs.fields)
                
                # Standardize column names
                df.columns = df.columns.str.lower().str.strip()
                
                # Create mapping for baostock columns
                column_mapping = {
                    'date': 'date',
                    'open': 'open',
                    'high': 'high',
                    'low': 'low',
                    'close': 'close',
                    'volume': 'volume',
                }
                
                # Rename columns
                df = df.rename(columns=column_mapping)
                
                # Filter to required columns
                required_cols = ['date', 'open', 'high', 'low', 'close', 'volume']
                available_cols = [col for col in required_cols if col in df.columns]
                
                if len(available_cols) < 5:
                    return None
                    
                df = df[available_cols]
                
                # Convert date column
                if 'date' in df.columns:
                    df['date'] = pd.to_datetime(df['date'])
                    df = df.set_index('date')
                    df = df.sort_index()
                
                # Convert numeric columns to float
                for col in ['open', 'high', 'low', 'close', 'volume']:
                    if col in df.columns:
                        df[col] = pd.to_numeric(df[col], errors='coerce')
                
                # Remove NaN rows
                df = df.dropna()
                
                if len(df) < 50:
                    return None
                
                # Keep only last period_days
                df = df.tail(period_days)
                
                # Rename to match yfinance format (OHLCV)
                df = df.rename(columns={
                    'open': 'Open',
                    'high': 'High',
                    'low': 'Low',
                    'close': 'Close',
                    'volume': 'Volume'
                })
                
                return df
                
            finally:
                # Restore stderr
                sys.stderr = old_stderr
        
        except Exception as e:
            # Silently fail - errors are expected for delisted stocks
            return None

# ============================================================================
# BENCHMARK & RELATIVE STRENGTH
# ============================================================================
_benchmark_cache = {}
_benchmark_lock = threading.Lock()  # Thread-safe benchmark cache access
_ticker_cache_lock = threading.Lock()  # Thread-safe ticker cache access
_benchmark_hist = None  # Global benchmark data, set before scanning

def get_benchmark_data(symbol="SPY", period="1y"):
    """Fetch and cache benchmark data for RS calculation (thread-safe)"""
    # Thread-safe cache check
    with _benchmark_lock:
        if symbol in _benchmark_cache:
            return _benchmark_cache[symbol]
    # Fetch outside lock to allow concurrent network I/O
    try:
        data = yf.Ticker(symbol).history(period=period)
        if data is not None and not data.empty:
            with _benchmark_lock:
                _benchmark_cache[symbol] = data
            return data
    except Exception:
        pass
    return None

def get_benchmark_for_ticker(ticker):
    """Return the appropriate benchmark symbol based on ticker's market suffix"""
    for suffix, benchmark in RS_BENCHMARK_MAP.items():
        if ticker.upper().endswith(suffix.upper()):
            return benchmark
    return RS_BENCHMARK

def get_zigzag_pct_for_ticker(ticker):
    """Return the appropriate Zig Zag threshold based on ticker's market suffix"""
    for suffix, pct in ZIGZAG_PCT_MAP.items():
        if ticker.upper().endswith(suffix.upper()):
            return pct
    return ZIGZAG_PCT

def calculate_rs_rating(stock_hist, benchmark_hist, period=None):
    """Calculate relative strength: stock excess return vs benchmark.
    
    Returns excess return (%) over benchmark. Positive = outperforming.
    Uses independent last-N-days for each (handles different trading calendars).
    """
    if period is None:
        period = RS_PERIOD
    if benchmark_hist is None or len(stock_hist) < period // 2:
        return None
    
    stock_period = min(period, len(stock_hist) - 1)
    bench_period = min(period, len(benchmark_hist) - 1)
    
    if stock_period < 20 or bench_period < 20:
        return None
    
    stock_return = (stock_hist['Close'].iloc[-1] / stock_hist['Close'].iloc[-stock_period] - 1) * 100
    bench_return = (benchmark_hist['Close'].iloc[-1] / benchmark_hist['Close'].iloc[-bench_period] - 1) * 100
    
    return round(stock_return - bench_return, 1)

# ============================================================================
# VCP DETECTION FUNCTIONS
# ============================================================================
def find_swing_points(df, pct=None):
    """Find swing highs and lows using the Zig Zag algorithm.
    
    Identifies significant price reversals by requiring a minimum percentage
    move before registering a new swing point. This naturally filters market
    noise without any external dependencies.
    
    Args:
        df: DataFrame with 'High' and 'Low' columns
        pct: Minimum reversal % to register a new swing (default: ZIGZAG_PCT)
    
    Returns:
        (swing_highs, swing_lows) - lists of {'index', 'price', 'date'} dicts
    """
    if pct is None:
        pct = ZIGZAG_PCT
    
    highs_arr = df['High'].values
    lows_arr = df['Low'].values
    n = len(df)
    
    if n < 3:
        return [], []
    
    pivots = []  # (index, price, 'H' or 'L')
    
    # ── Phase 1: Determine initial trend direction ──
    # Track running high/low from bar 0 until a significant move appears
    running_high = highs_arr[0]
    running_high_idx = 0
    running_low = lows_arr[0]
    running_low_idx = 0
    trend = 0  # 1 = up, -1 = down (0 = undetermined)
    scan_start = 1
    
    for i in range(1, n):
        if highs_arr[i] > running_high:
            running_high = highs_arr[i]
            running_high_idx = i
        if lows_arr[i] < running_low:
            running_low = lows_arr[i]
            running_low_idx = i
        
        up_pct = (running_high - lows_arr[0]) / lows_arr[0] * 100 if lows_arr[0] > 0 else 0
        down_pct = (highs_arr[0] - running_low) / highs_arr[0] * 100 if highs_arr[0] > 0 else 0
        
        if up_pct >= pct and up_pct >= down_pct:
            # First significant move was UP → first pivot is the starting low
            pivots.append((0, lows_arr[0], 'L'))
            trend = 1
            # Reset tracking from the high we found
            running_low = lows_arr[running_high_idx]
            running_low_idx = running_high_idx
            scan_start = running_high_idx + 1
            break
        elif down_pct >= pct:
            # First significant move was DOWN → first pivot is the starting high
            pivots.append((0, highs_arr[0], 'H'))
            trend = -1
            running_high = highs_arr[running_low_idx]
            running_high_idx = running_low_idx
            scan_start = running_low_idx + 1
            break
    
    if trend == 0:
        return [], []  # No significant move in the data
    
    # ── Phase 2: Walk forward, alternating between highs and lows ──
    for i in range(scan_start, n):
        if trend == 1:  # In uptrend — tracking higher highs
            if highs_arr[i] > running_high:
                running_high = highs_arr[i]
                running_high_idx = i
            
            # Check for reversal down from the running high
            drop_pct = (running_high - lows_arr[i]) / running_high * 100 if running_high > 0 else 0
            if drop_pct >= pct:
                # Confirm the high as a pivot, switch to downtrend
                pivots.append((running_high_idx, running_high, 'H'))
                trend = -1
                running_low = lows_arr[i]
                running_low_idx = i
                running_high = highs_arr[i]
                running_high_idx = i
        
        else:  # trend == -1, in downtrend — tracking lower lows
            if lows_arr[i] < running_low:
                running_low = lows_arr[i]
                running_low_idx = i
            
            # Check for reversal up from the running low
            rise_pct = (highs_arr[i] - running_low) / running_low * 100 if running_low > 0 else 0
            if rise_pct >= pct:
                # Confirm the low as a pivot, switch to uptrend
                pivots.append((running_low_idx, running_low, 'L'))
                trend = 1
                running_high = highs_arr[i]
                running_high_idx = i
                running_low = lows_arr[i]
                running_low_idx = i
    
    # ── Convert to output format ──
    swing_highs = [{'index': idx, 'price': price, 'date': df.index[idx]}
                   for idx, price, ptype in pivots if ptype == 'H']
    swing_lows = [{'index': idx, 'price': price, 'date': df.index[idx]}
                  for idx, price, ptype in pivots if ptype == 'L']
    
    return swing_highs, swing_lows

def calculate_contraction_depth(high_val, low_val):
    """Calculate the depth of a price contraction"""
    return ((high_val - low_val) / high_val) * 100

def detect_vcp_pattern(df, rs_rating=None, rs_rating_long=None, zigzag_pct=None):
    """Main VCP pattern detection logic"""
    
    if len(df) < LOOKBACK_PERIOD:
        return {
            'is_vcp': False,
            'reason': f'Insufficient data ({len(df)} days)',
            'contractions': 0,
            'quality_score': 0
        }
    
    # Work on a copy to avoid mutating cached data
    df = df.copy()
    
    # Calculate indicators
    df['MA'] = df['Close'].rolling(window=TREND_MA_PERIOD).mean()
    df['Volume_MA'] = df['Volume'].rolling(window=VOLUME_MA_PERIOD).mean()
    
    # Check trend
    last_close = df['Close'].iloc[-1]
    last_ma = df['MA'].iloc[-1]
    price_above_ma_pct = ((last_close - last_ma) / last_ma) * 100
    in_uptrend = price_above_ma_pct >= MIN_PRICE_ABOVE_MA
    
    if not in_uptrend:
        return {
            'is_vcp': False,
            'reason': f'Not in uptrend (only {price_above_ma_pct:.1f}% above MA)',
            'contractions': 0,
            'quality_score': 0,
            'price_above_ma': price_above_ma_pct
        }
    
    # Find swing points (store lookback_df for per-contraction volume analysis)
    lookback_df = df.tail(LOOKBACK_PERIOD).copy().reset_index(drop=True)
    highs, lows = find_swing_points(lookback_df, pct=zigzag_pct)
    
    if len(highs) < MIN_CONTRACTIONS + 1 or len(lows) < MIN_CONTRACTIONS:
        return {
            'is_vcp': False,
            'reason': f'Insufficient pivots (H:{len(highs)}, L:{len(lows)})',
            'contractions': 0,
            'quality_score': 0,
            'price_above_ma': price_above_ma_pct
        }
    
    # Check for progressive contractions + measure volume per contraction
    contractions = []
    contraction_volumes = []  # Average volume during each contraction period
    recent_highs = highs[-min(MAX_CONTRACTIONS + 1, len(highs)):]
    recent_lows = lows[-min(MAX_CONTRACTIONS, len(lows)):]
    
    for i in range(min(len(recent_highs) - 1, len(recent_lows))):
        high_price = recent_highs[i]['price']
        low_price = recent_lows[i]['price']
        depth = calculate_contraction_depth(high_price, low_price)
        contractions.append(depth)
        
        # Average volume during this contraction period (high → low)
        h_idx = recent_highs[i]['index']
        l_idx = recent_lows[i]['index']
        start, end = min(h_idx, l_idx), max(h_idx, l_idx)
        if end > start and end < len(lookback_df):
            vol = lookback_df['Volume'].iloc[start:end+1].mean()
            contraction_volumes.append(vol)
        else:
            contraction_volumes.append(0)
    
    # Filter out micro-oscillations (noise) - keep only meaningful swings
    filtered = [(c, v) for c, v in zip(contractions, contraction_volumes)
                if c >= MIN_SWING_DEPTH_PCT]
    if len(filtered) > 0:
        contractions, contraction_volumes = zip(*filtered)
        contractions = list(contractions)
        contraction_volumes = list(contraction_volumes)
    else:
        contractions = []
        contraction_volumes = []
    
    if len(contractions) < MIN_CONTRACTIONS:
        return {
            'is_vcp': False,
            'reason': f'Too few significant contractions ({len(contractions)} after noise filter)',
            'contractions': len(contractions),
            'quality_score': 0,
            'price_above_ma': price_above_ma_pct
        }
    
    # Safety check: ensure contractions list is valid before accessing elements
    if not contractions or len(contractions) == 0:
        return {
            'is_vcp': False,
            'reason': 'No valid contractions after filtering',
            'contractions': 0,
            'quality_score': 0,
            'price_above_ma': price_above_ma_pct
        }
    
    # Verify contractions are getting progressively smaller (reverse scan)
    # Allows CONTRACTION_NOISE_TOLERANCE waves with minor deviation
    valid_contractions = 1  # Last contraction is always valid
    noise_used = 0
    
    for i in range(len(contractions) - 1, 0, -1):
        if contractions[i] < contractions[i-1] * CONTRACTION_RATIO:
            valid_contractions += 1
        elif noise_used < CONTRACTION_NOISE_TOLERANCE and \
             contractions[i] < contractions[i-1] * (CONTRACTION_RATIO + CONTRACTION_NOISE_SLACK):
            valid_contractions += 1
            noise_used += 1
        else:
            break
    
    if valid_contractions < MIN_CONTRACTIONS:
        return {
            'is_vcp': False,
            'reason': f'Contractions not progressive ({valid_contractions} valid of {len(contractions)} waves)',
            'contractions': valid_contractions,
            'quality_score': 0,
            'price_above_ma': price_above_ma_pct
        }
    
    # Check final contraction is tight (the "squeeze" before breakout)
    last_contraction = contractions[-1]
    if last_contraction > MAX_LAST_CONTRACTION:
        return {
            'is_vcp': False,
            'reason': f'Last contraction too wide ({last_contraction:.1f}% > {MAX_LAST_CONTRACTION}%)',
            'contractions': valid_contractions,
            'quality_score': 0,
            'price_above_ma': price_above_ma_pct
        }
    
    # Check overall narrowing: first progressive contraction must be significantly > last
    first_in_chain = contractions[len(contractions) - valid_contractions]
    if first_in_chain < last_contraction * MIN_OVERALL_NARROWING:
        return {
            'is_vcp': False,
            'reason': f'Pattern not narrowing enough ({first_in_chain:.1f}% → {last_contraction:.1f}%)',
            'contractions': valid_contractions,
            'quality_score': 0,
            'price_above_ma': price_above_ma_pct
        }
    
    # Check volume pattern (both overall AND per-contraction)
    recent_vol_avg = df['Volume'].tail(10).mean()
    avg_volume = df['Volume_MA'].iloc[-1]
    volume_decreasing = recent_vol_avg < avg_volume
    
    # Per-contraction volume: volume should dry up in each successive pullback
    vol_contracting = False
    if len(contraction_volumes) >= 2:
        vol_dec_count = sum(1 for i in range(1, len(contraction_volumes))
                           if contraction_volumes[i] < contraction_volumes[i-1])
        vol_contracting = vol_dec_count >= len(contraction_volumes) // 2
    
    if REQUIRE_DECREASING_VOLUME and not (volume_decreasing or vol_contracting):
        return {
            'is_vcp': False,
            'reason': 'Volume not decreasing (overall or per-contraction)',
            'contractions': valid_contractions,
            'quality_score': 0,
            'price_above_ma': price_above_ma_pct
        }
    
    # Check for breakout (expanded window)
    pivot_high = df['High'].tail(PIVOT_LOOKBACK).max()
    current_close = df['Close'].iloc[-1]
    is_breakout = False
    for day_offset in range(1, min(BREAKOUT_LOOKBACK_DAYS + 1, len(df))):
        close_today = df['Close'].iloc[-day_offset]
        close_prev = df['Close'].iloc[-day_offset - 1] if day_offset + 1 <= len(df) else 0
        if close_today > pivot_high and close_prev <= pivot_high:
            is_breakout = True
            break
    
    current_volume = df['Volume'].iloc[-1]
    recent_3d_vol = df['Volume'].tail(3).mean() if len(df) >= 3 else current_volume
    volume_spike = (current_volume > avg_volume * BREAKOUT_VOLUME_MULTIPLIER or
                    recent_3d_vol > avg_volume * BREAKOUT_VOLUME_MULTIPLIER * 0.9)
    sustained_volume = recent_3d_vol > avg_volume * SUSTAINED_VOLUME_MULTIPLIER  # 3-day sustained above MA
    
    # Calculate distance to pivot
    distance_to_pivot = ((pivot_high - current_close) / current_close) * 100
    
    # ── Quality Score (0-100) with weighted components ──
    q = {}
    
    # Contractions (max 25): more progressive waves = better
    q['contractions'] = min(valid_contractions * 7, 25)
    
    # Trend strength (max 20): how far above MA
    if price_above_ma_pct > 15:
        q['trend'] = 20
    elif price_above_ma_pct > 8:
        q['trend'] = 15
    elif price_above_ma_pct > 3:
        q['trend'] = 10
    else:
        q['trend'] = 5
    
    # Volume pattern (max 20): per-contraction dryup + overall
    if vol_contracting and volume_decreasing and recent_vol_avg < avg_volume * 0.7:
        q['volume'] = 20
    elif vol_contracting and volume_decreasing:
        q['volume'] = 15
    elif vol_contracting or volume_decreasing:
        q['volume'] = 10
    else:
        q['volume'] = 0
    
    # Tightness (max 15): how tight the final contraction is
    if last_contraction < 3:
        q['tightness'] = 15
    elif last_contraction < 6:
        q['tightness'] = 10
    elif last_contraction < 10:
        q['tightness'] = 5
    else:
        q['tightness'] = 0
    
    # Relative Strength — short-term RS63 (max 20)
    if rs_rating is not None:
        if rs_rating > 15:
            q['rs'] = 20
        elif rs_rating > 8:
            q['rs'] = 15
        elif rs_rating > 0:
            q['rs'] = 10
        elif rs_rating > -5:
            q['rs'] = 5
        else:
            q['rs'] = 0
    else:
        q['rs'] = 10  # Unknown benchmark = neutral
    
    # Sustained leadership bonus — long-term RS126 (max 10, bonus on top)
    if rs_rating_long is not None:
        if rs_rating_long > 20:
            q['rs_long'] = 10
        elif rs_rating_long > 10:
            q['rs_long'] = 7
        elif rs_rating_long > 0:
            q['rs_long'] = 4
        else:
            q['rs_long'] = 0
    else:
        q['rs_long'] = 0
    
    quality_score = min(sum(q.values()), 100)
    
    return {
        'is_vcp': True,
        'reason': 'VCP detected',
        'contractions': valid_contractions,
        'quality_score': int(quality_score),
        'price_above_ma': price_above_ma_pct,
        'volume_decreasing': volume_decreasing,
        'vol_contracting': vol_contracting,
        'is_breakout': is_breakout,
        'volume_spike': volume_spike,
        'sustained_volume': sustained_volume,
        'distance_to_pivot': distance_to_pivot,
        'last_contraction_depth': contractions[-1] if contractions else 0,
        'pivot_high': pivot_high,
        'current_price': current_close,
        'rs_rating': rs_rating
    }

# ============================================================================
# SINGLE TICKER ANALYSIS
# ============================================================================
def analyze_ticker(ticker, ticker_cache=None):
    """Analyze a single ticker for VCP pattern
    
    Supports:
    - US stocks (AAPL, MSFT, etc.)
    - China A-shares (.SS Shanghai, .SZ Shenzhen)
    - Uses Baostock as fallback when yfinance fails on China stocks
    - Uses cache to avoid redundant downloads
    """
    hist = None
    yf_succeeded = False
    stock = None
    
    # Check cache first (thread-safe read)
    if ticker_cache is not None:
        with _ticker_cache_lock:
            if ticker in ticker_cache:
                hist = ticker_cache[ticker]
                yf_succeeded = True
    
    if not yf_succeeded:
        # First try yfinance
        try:
            stock = yf.Ticker(ticker)
            hist = stock.history(period=HISTORY_PERIOD)
            
            # Validate we got data back
            if hist is None or hist.empty:
                hist = None
            else:
                yf_succeeded = True
        except Exception:
            hist = None
    
        # If yfinance failed and it's a China stock (.SS or .SZ), try Baostock
        if hist is None and (ticker.endswith('.SS') or ticker.endswith('.SZ')):
            hist = fetch_china_stock_baostock(ticker)
        
        # Cache the result if successful (thread-safe write)
        if hist is not None and ticker_cache is not None:
            with _ticker_cache_lock:
                ticker_cache[ticker] = hist
    
    # If still no data, return error status
    if hist is None or hist.empty:
        return {
            'Ticker': ticker,
            'Status': 'NO DATA',
            'VCP': False,
            'Quality': 0,
            'Contractions': 0,
            'Details': '❌ No price data found - double-check ticker'
        }
    
    # Check if we have enough data
    if len(hist) < 50:
        return {
            'Ticker': ticker,
            'Status': 'INSUFFICIENT DATA',
            'VCP': False,
            'Quality': 0,
            'Contractions': 0,
            'Details': f'Only {len(hist)} days available - verify ticker exists'
        }
    
    # Liquidity filter: skip illiquid/penny stocks
    if LIQUIDITY_FILTER_ENABLED:
        avg_vol = hist['Volume'].tail(VOLUME_MA_PERIOD).mean() if len(hist) >= VOLUME_MA_PERIOD else hist['Volume'].mean()
        last_price = hist['Close'].iloc[-1]
        
        if avg_vol < MIN_AVG_VOLUME:
            return {
                'Ticker': ticker,
                'Status': 'LOW LIQUIDITY',
                'VCP': False,
                'Quality': 0,
                'Contractions': 0,
                'Details': f'Avg volume {avg_vol:,.0f} < {MIN_AVG_VOLUME:,} minimum'
            }
        
        if last_price < MIN_PRICE:
            return {
                'Ticker': ticker,
                'Status': 'PENNY STOCK',
                'VCP': False,
                'Quality': 0,
                'Contractions': 0,
                'Details': f'Price ${last_price:.2f} < ${MIN_PRICE:.2f} minimum'
            }
    
    # Get stock info (safely - may fail for some tickers)
    name = 'N/A'
    try:
        if yf_succeeded and stock is not None:
            info = stock.info
            name = info.get('shortName', info.get('longName', 'N/A'))
        else:
            name = ticker  # For Baostock data, use ticker code as name
    except Exception:
        # stock.info fetching failed - use ticker as name
        name = ticker
    
    # Calculate RS rating vs market-appropriate benchmark (short + long term)
    ticker_benchmark = get_benchmark_for_ticker(ticker)
    benchmark_data = get_benchmark_data(ticker_benchmark)
    if benchmark_data is None:
        benchmark_data = _benchmark_hist
        ticker_benchmark = RS_BENCHMARK
    rs_rating = calculate_rs_rating(hist, benchmark_data, period=RS_PERIOD)
    rs_rating_long = calculate_rs_rating(hist, benchmark_data, period=RS_PERIOD_LONG)
    
    # Get per-market Zig Zag threshold
    ticker_zigzag = get_zigzag_pct_for_ticker(ticker)
    
    # Detect VCP (pass RS for quality scoring)
    vcp_result = detect_vcp_pattern(hist, rs_rating=rs_rating, rs_rating_long=rs_rating_long, zigzag_pct=ticker_zigzag)
    
    if vcp_result['is_vcp']:
        status = "🚀 BREAKOUT!" if vcp_result.get('is_breakout', False) else "⚠️ VCP FORMING"
    else:
        status = "No Pattern"
    
    return {
        'Ticker': ticker,
        'Name': name,
        'Status': status,
        'VCP': vcp_result['is_vcp'],
        'Quality': vcp_result['quality_score'],
        'Contractions': vcp_result['contractions'],
        'Price Above MA': vcp_result.get('price_above_ma', 0),
        'Distance to Pivot': vcp_result.get('distance_to_pivot', 0),
        'RS Rating': rs_rating if rs_rating is not None else 0,
        'RS Rating Long': rs_rating_long if rs_rating_long is not None else 0,
        'Breakout': vcp_result.get('is_breakout', False),
        'Volume Spike': vcp_result.get('volume_spike', False),
        'Sustained Volume': vcp_result.get('sustained_volume', False),
        'Benchmark': ticker_benchmark,
        'Current Price': vcp_result.get('current_price', 0),
        'Pivot Price': vcp_result.get('pivot_high', 0),
        'Details': vcp_result['reason']
    }

# ============================================================================
# MAIN SCANNING FUNCTION
# ============================================================================
def scan_watchlist(tickers, ticker_cache=None):
    """Scan a list of tickers for VCP patterns"""
    global _benchmark_hist
    
    if ticker_cache is None:
        ticker_cache = {}
    
    # Show swing detection method with per-market thresholds
    zz_markets = ', '.join(f'{s}: {p}%' for s, p in sorted(ZIGZAG_PCT_MAP.items()))
    console.print(f"[dim]🔬 Swing detection: Zig Zag (US: {ZIGZAG_PCT}%, {zz_markets})[/dim]")
    
    # Pre-fetch benchmark data for RS calculation (per-market)
    benchmarks_needed = {RS_BENCHMARK}
    for t in tickers:
        benchmarks_needed.add(get_benchmark_for_ticker(t))
    
    for bm in sorted(benchmarks_needed):
        data = get_benchmark_data(bm)
        if data is not None:
            console.print(f"[dim]✓ {bm} benchmark: {len(data)} trading days loaded[/dim]")
        else:
            console.print(f"[yellow]⚠️  Could not load {bm} — RS unavailable for that market[/yellow]")
    
    _benchmark_hist = get_benchmark_data(RS_BENCHMARK)
    
    # Filter out index tickers and invalid symbols
    valid_tickers = []
    skipped_tickers = []
    
    for ticker in tickers:
        # Skip index tickers (start with ^) and symbols with ! (invalid)
        if ticker.startswith('^') or '!' in ticker:
            skipped_tickers.append(ticker)
        else:
            valid_tickers.append(ticker)
    
    console.print(f"\n[bold cyan]{'='*80}[/bold cyan]")
    console.print(f"[bold cyan]VCP Pattern Scanner - Scanning {len(valid_tickers)} tickers[/bold cyan]")
    if skipped_tickers:
        console.print(f"[dim]Skipped {len(skipped_tickers)} index/invalid tickers: {', '.join(skipped_tickers[:5])}{'...' if len(skipped_tickers) > 5 else ''}[/dim]")
    console.print(f"[bold cyan]{'='*80}[/bold cyan]")
    
    data = []
    
    with Progress(
        SpinnerColumn(),
        TextColumn("[progress.description]{task.description}"),
        console=console
    ) as progress:
        task = progress.add_task(f"[cyan]Analyzing tickers...", total=len(valid_tickers))
        
        with ThreadPoolExecutor(max_workers=MAX_WORKERS) as executor:
            futures = {executor.submit(analyze_ticker, ticker, ticker_cache): ticker for ticker in valid_tickers}
            
            for future in as_completed(futures):
                result = future.result()
                data.append(result)
                progress.advance(task)
    
    # Convert to DataFrame
    df = pd.DataFrame(data)
    
    # Sort: Breakouts first, then by quality score
    df['Breakout_rank'] = df['Breakout'].map({True: 2, False: 0})
    df['VCP_rank'] = df['VCP'].map({True: 1, False: 0})
    df = df.sort_values(
        by=['Breakout_rank', 'VCP_rank', 'Quality'],
        ascending=[False, False, False]
    ).reset_index(drop=True)
    df = df.drop(columns=['Breakout_rank', 'VCP_rank'])
    
    return df

# ============================================================================
# DISPLAY RESULTS
# ============================================================================
def display_results(df):
    """Display VCP scan results in a nice table"""
    
    # Filter for VCP patterns only
    vcp_stocks = df[df['VCP'] == True].copy()
    
    if len(vcp_stocks) == 0:
        console.print("\n[yellow]No VCP patterns detected in watchlist[/yellow]")
        
        # Diagnostic breakdown: show where tickers were eliminated
        console.print(f"\n[bold yellow]📋 Failure Breakdown ({len(df)} tickers scanned):[/bold yellow]")
        reasons = {
            'No data available':     df['Details'].str.contains('No price data|double-check', case=False, na=False).sum(),
            'Insufficient history':  df['Details'].str.contains('Insufficient data|Only.*days', case=False, na=False).sum(),
            'Low liquidity':         df['Details'].str.contains('Avg volume.*minimum|LOW LIQUIDITY', case=False, na=False).sum(),
            'Penny stock':           df['Details'].str.contains('Price.*minimum|PENNY STOCK', case=False, na=False).sum(),
            'Not in uptrend':        df['Details'].str.contains('Not in uptrend', case=False, na=False).sum(),
            'Too few swing pivots':  df['Details'].str.contains('Insufficient pivots|Too few significant|No valid contractions', case=False, na=False).sum(),
            'Not progressive':       df['Details'].str.contains('not progressive', case=False, na=False).sum(),
            'Last wave too wide':    df['Details'].str.contains('too wide', case=False, na=False).sum(),
            'Not narrowing enough':  df['Details'].str.contains('not narrowing', case=False, na=False).sum(),
            'Volume not decreasing': df['Details'].str.contains('Volume not', case=False, na=False).sum(),
        }
        for label, count in reasons.items():
            if count > 0:
                color = "red" if 'No data' in label or 'Insufficient' in label else "yellow" if 'uptrend' in label or 'pivot' in label else "cyan"
                console.print(f"  [{color}]• {label:<24} {count:>4}[/{color}]")
        
        # Near misses - stocks that failed ONLY on volume (passed everything else)
        near_miss = df[df['Details'].str.contains('Volume not', case=False, na=False)]
        if len(near_miss) > 0:
            console.print(f"\n[bold cyan]🔍 Near Misses (passed all checks except volume):[/bold cyan]")
            for _, row in near_miss.head(10).iterrows():
                console.print(f"  • {row['Ticker']:<12} Waves: {row['Contractions']}")
        
        # Near misses - stocks closest to progressive contractions
        near_prog = df[df['Details'].str.contains('not progressive|too wide|not narrowing', case=False, na=False)]
        if len(near_prog) > 0:
            near_prog_sorted = near_prog.sort_values('Contractions', ascending=False)
            console.print(f"\n[bold cyan]🔍 Best Contraction Attempts (not fully progressive):[/bold cyan]")
            for _, row in near_prog_sorted.head(10).iterrows():
                console.print(f"  • {row['Ticker']:<12} Valid waves: {row['Contractions']}")
        
        return
    
    # ── Prime VCPs: institutional-quality subset ──
    prime_vcps = vcp_stocks[
        (vcp_stocks['Quality'] >= 70) &
        (vcp_stocks['RS Rating'] > 5) &
        (vcp_stocks['RS Rating Long'] > 0) &
        (vcp_stocks['Distance to Pivot'] < 10)
    ].copy()
    
    other_vcps = vcp_stocks[~vcp_stocks.index.isin(prime_vcps.index)].copy()
    
    # Display Prime VCPs first
    if len(prime_vcps) > 0:
        console.print(f"\n[bold green]⭐ {len(prime_vcps)} Prime VCP(s) (Quality≥70, RS63>5, RS126>0, <10% to pivot)[/bold green]\n")
        _print_vcp_table(prime_vcps, is_prime=True)
    else:
        console.print(f"\n[yellow]No Prime VCP (0 prime ⭐)[/yellow]")
    
    # Then show remaining VCPs
    if len(other_vcps) > 0:
        console.print(f"\n[bold yellow]📋 {len(other_vcps)} Watch VCP(s)[/bold yellow]\n")
        _print_vcp_table(other_vcps, is_prime=False)
    
    if len(prime_vcps) == 0 and len(other_vcps) == 0:
        console.print(f"\n[bold green]✓ Found {len(vcp_stocks)} VCP Pattern(s)![/bold green]\n")
        _print_vcp_table(vcp_stocks, is_prime=False)
    
    # Summary stats
    console.print(f"\n[bold cyan]📊 Summary:[/bold cyan]")
    console.print(f"  • Total VCP patterns: {len(vcp_stocks)} ({len(prime_vcps)} prime ⭐)")
    console.print(f"  • Active breakouts: {len(vcp_stocks[vcp_stocks['Breakout'] == True])}")
    sustained_n = int(vcp_stocks['Sustained Volume'].sum()) if 'Sustained Volume' in vcp_stocks.columns else 0
    if sustained_n > 0:
        console.print(f"  • Sustained breakout volume (📊): {sustained_n}")
    console.print(f"  • High quality (75%+): {len(vcp_stocks[vcp_stocks['Quality'] >= 75])}")
    console.print(f"  • Near pivot (<2%): {len(vcp_stocks[abs(vcp_stocks['Distance to Pivot']) < 2])}")
    if 'Benchmark' in vcp_stocks.columns:
        bms = ', '.join(sorted(b.lstrip('^') for b in vcp_stocks['Benchmark'].unique()))
        console.print(f"  • RS benchmarks used: {bms}")
    
    # Save to HTML (pass prime list for highlighting)
    today = datetime.now().strftime("%Y-%m-%d")
    report_folder = Path(__file__).parent / 'Report'
    report_folder.mkdir(parents=True, exist_ok=True)  # Create if doesn't exist
    
    filename = f"VCP_Scan_{today}.html"
    filepath = report_folder / filename
    
    save_vcp_to_html(vcp_stocks, str(filepath), prime_tickers=set(prime_vcps['Ticker']) if len(prime_vcps) > 0 else set())
    
    # Save to master Excel log
    save_vcp_to_master_log(vcp_stocks, report_folder)
    
    # Save to CSV
    csv_filepath = report_folder / f"VCP_Scan_{today}.csv"
    vcp_stocks.to_csv(csv_filepath, index=False)
    console.print(f"[green]✅ CSV report saved to ./Report/{csv_filepath.name}[/green]")

def _print_vcp_table(stocks_df, is_prime=False):
    """Print a VCP results table (reused for Prime and Other sections)"""
    table = Table(show_header=True, header_style="bold magenta", box=None)
    table.add_column("Ticker", width=10, style="bold white")
    table.add_column("Name", width=22)
    table.add_column("Status", width=15)
    table.add_column("Quality", justify="right", width=8)
    table.add_column("Waves", justify="center", width=6)
    table.add_column("RS63\nvs Mkt", justify="right", width=9)
    table.add_column("RS126\nvs Mkt", justify="right", width=9)
    table.add_column("Price\nvs MA50", justify="right", width=8)
    table.add_column("To\nPivot", justify="right", width=7)
    table.add_column("Current\nPrice", justify="right", width=10)
    table.add_column("Pivot\nPrice", justify="right", width=10)
    
    for _, row in stocks_df.iterrows():
        sustained = row.get('Sustained Volume', False)
        if row['Breakout']:
            vol_mark = " 📊" if sustained else ""
            status_str = f"[bold green]🚀 BREAKOUT{vol_mark}[/bold green]"
            row_style = "black on green"
        else:
            vol_mark = " 📊" if sustained else ""
            status_str = f"[yellow]⚠️ FORMING{vol_mark}[/yellow]"
            row_style = None
        
        quality = row['Quality']
        if quality >= 75:
            quality_str = f"[bold green]{quality}%[/bold green]"
        elif quality >= 50:
            quality_str = f"[yellow]{quality}%[/yellow]"
        else:
            quality_str = f"[dim]{quality}%[/dim]"
        
        dist = row['Distance to Pivot']
        if dist < 0:
            dist_str = f"[green]✓ +{abs(dist):.1f}%[/green]"
        elif dist < 2:
            dist_str = f"[yellow]{dist:.1f}%[/yellow]"
        else:
            dist_str = f"[dim]{dist:.1f}%[/dim]"
        
        pct_ma = row['Price Above MA']
        pct_ma_str = f"[green]+{pct_ma:.1f}%[/green]" if pct_ma > 0 else f"[red]{pct_ma:.1f}%[/red]"
        
        # RS63 color
        rs = row.get('RS Rating', 0)
        if rs > 10:
            rs_str = f"[bold green]+{rs:.1f}%[/bold green]"
        elif rs > 0:
            rs_str = f"[green]+{rs:.1f}%[/green]"
        elif rs > -5:
            rs_str = f"[yellow]{rs:.1f}%[/yellow]"
        else:
            rs_str = f"[red]{rs:.1f}%[/red]"
        
        # RS126 color
        rs_l = row.get('RS Rating Long', 0)
        if rs_l > 10:
            rs_l_str = f"[bold green]+{rs_l:.1f}%[/bold green]"
        elif rs_l > 0:
            rs_l_str = f"[green]+{rs_l:.1f}%[/green]"
        elif rs_l > -5:
            rs_l_str = f"[yellow]{rs_l:.1f}%[/yellow]"
        else:
            rs_l_str = f"[red]{rs_l:.1f}%[/red]"
        
        table.add_row(
            row['Ticker'],
            str(row['Name'])[:22],
            status_str,
            quality_str,
            str(row['Contractions']),
            rs_str,
            rs_l_str,
            pct_ma_str,
            dist_str,
            f"${row['Current Price']:.2f}",
            f"${row['Pivot Price']:.2f}",
            style=row_style
        )
    
    console.print(table)

# ============================================================================
# SAVE RESULTS
# ============================================================================
def save_vcp_to_html(df, filepath, prime_tickers=None):
    """Convert VCP results DataFrame to formatted HTML - matches terminal display"""
    try:
        html_content = f"""
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>VCP Pattern Scanner Results</title>
    <style>
        body {{
            font-family: 'Monospace', 'Courier New', monospace;
            background-color: #1e1e1e;
            color: #d4d4d4;
            padding: 20px;
        }}
        h1 {{
            color: #9966cc;
            border-bottom: 2px solid #9966cc;
            padding-bottom: 10px;
        }}
        .summary {{
            background-color: #2d2d2d;
            padding: 15px;
            border-left: 4px solid #9966cc;
            margin: 20px 0;
            border-radius: 4px;
        }}
        table {{
            width: 100%;
            border-collapse: collapse;
            margin-top: 20px;
        }}
        th {{
            background-color: #9966cc;
            color: white;
            padding: 10px;
            text-align: left;
            font-weight: bold;
            border: 1px solid #7744aa;
        }}
        td {{
            padding: 8px 10px;
            border: 1px solid #3d3d3d;
            background-color: #252525;
        }}
        tr:hover {{
            background-color: #2d2d2d;
        }}
        .breakout {{
            color: #4ec9b0;
            font-weight: bold;
        }}
        .forming {{
            color: #dcdcaa;
            font-weight: bold;
        }}
        .error {{
            color: #f48771;
        }}
        .ticker {{
            font-weight: bold;
            color: #9cdcfe;
        }}
        .timestamp {{
            color: #858585;
            font-size: 0.9em;
        }}
        .right {{ text-align: right; }}
        .center {{ text-align: center; }}
    </style>
</head>
<body>
    <h1>VCP Pattern Scanner Results</h1>
    <div class="timestamp">Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}</div>
    
    <div class="summary">
        <strong>Summary:</strong><br>
        Total Patterns: {len(df)}<br>
        Breakouts: {len(df[df['Status'].str.contains('BREAKOUT', case=False, na=False)])}<br>
        Forming: {len(df[df['Status'].str.contains('FORMING', case=False, na=False)])}<br>
        High Quality (75%+): {len(df[df['Quality'] >= 75])}<br>
        Near Pivot (&lt;2%): {len(df[abs(df['Distance to Pivot']) < 2])}
    </div>
    
    <table>
        <thead>
            <tr>
                <th>Ticker</th>
                <th>Name</th>
                <th>Status</th>
                <th class="center">Quality</th>
                <th class="center">Waves</th>
                <th class="right">RS63 vs Benchmark</th>
                <th class="right">RS126 vs Benchmark</th>
                <th class="right">Price vs MA50</th>
                <th class="right">To Pivot</th>
                <th class="right">Current Price</th>
                <th class="right">Pivot Price</th>
            </tr>
        </thead>
        <tbody>
"""
        
        for _, row in df.iterrows():
            ticker = str(row['Ticker'])[:12]
            name = str(row['Name'])[:40]
            status = str(row['Status'])
            
            # Format status with color
            if 'BREAKOUT' in status:
                status_html = '<span class="breakout">▲ BREAKOUT</span>'
            elif 'FORMING' in status:
                status_html = '<span class="forming">▲ FORMING</span>'
            else:
                status_html = '<span class="error">❌ ERROR</span>'
            
            is_prime = prime_tickers and ticker in prime_tickers
            prime_badge = '⭐ ' if is_prime else ''
            quality = f"{row['Quality']:.0f}%"
            contractions = str(row['Contractions'])
            rs_val = row.get('RS Rating', 0)
            rs_long_val = row.get('RS Rating Long', 0)
            bm_label = str(row.get('Benchmark', 'SPY')).lstrip('^') if 'Benchmark' in df.columns else 'SPY'
            rs_html = f"+{rs_val:.1f}% vs {bm_label}" if rs_val > 0 else f"{rs_val:.1f}% vs {bm_label}"
            rs_long_html = f"+{rs_long_val:.1f}% vs {bm_label}" if rs_long_val > 0 else f"{rs_long_val:.1f}% vs {bm_label}"
            price_ma = f"+{row['Price Above MA']:.1f}%" if row['Price Above MA'] > 0 else f"{row['Price Above MA']:.1f}%"
            distance = f"{row['Distance to Pivot']:.1f}%"
            price = f"${row['Current Price']:.2f}"
            pivot = f"${row['Pivot Price']:.2f}"
            
            row_bg = 'background-color: #1a2e1a;' if is_prime else ''
            html_content += f"""
            <tr style="{row_bg}">
                <td><span class="ticker">{prime_badge}{ticker}</span></td>
                <td>{name}</td>
                <td>{status_html}</td>
                <td class="center">{quality}</td>
                <td class="center">{contractions}</td>
                <td class="right">{rs_html}</td>
                <td class="right">{rs_long_html}</td>
                <td class="right">{price_ma}</td>
                <td class="right">{distance}</td>
                <td class="right">{price}</td>
                <td class="right">{pivot}</td>
            </tr>
"""
        
        html_content += """
        </tbody>
    </table>
</body>
</html>
"""
        
        with open(filepath, 'w', encoding='utf-8') as f:
            f.write(html_content)
        
        # Show relative path for sharing
        rel_path = Path(filepath).relative_to(SCRIPT_DIR) if Path(filepath).is_relative_to(SCRIPT_DIR) else Path(filepath).name
        console.print(f"[green]✅ HTML report saved to ./Report/{rel_path.name}[/green]")
    except Exception as e:
        console.print(f"[red]Error saving HTML:[/red]")
        console.print(f"[red]{type(e).__name__}: {str(e)}[/red]")
        console.print(f"[dim]{traceback.format_exc()}[/dim]")

def save_vcp_to_master_log(df, report_folder):
    """Append VCP results to a rolling master Excel log"""
    try:
        master_log_path = report_folder / "VCP_Master_Log.xlsx"
        today = datetime.now().strftime("%Y-%m-%d")
        
        # Add scan date column
        df_copy = df.copy()
        df_copy.insert(0, 'Scan Date', today)
        
        # Reorder columns for readability
        cols_to_keep = ['Scan Date', 'Ticker', 'Name', 'Status', 'Quality', 'Contractions',
                        'RS Rating', 'RS Rating Long', 'Price Above MA', 'Distance to Pivot', 'Current Price', 'Pivot Price']
        df_copy = df_copy[[col for col in cols_to_keep if col in df_copy.columns]]
        
        # Rename columns for Excel (safely map based on actual columns present)
        rename_map = {
            'Scan Date': 'Scan Date', 'Ticker': 'Ticker', 'Name': 'Company Name',
            'Status': 'Pattern Status', 'Quality': 'Quality %', 'Contractions': 'Wave Count',
            'RS Rating': 'RS63 vs Benchmark %', 'RS Rating Long': 'RS126 vs Benchmark %',
            'Price Above MA': 'Price vs MA50 %', 'Distance to Pivot': 'Distance to Pivot %',
            'Current Price': 'Current Price ($)', 'Pivot Price': 'Pivot Price ($)'
        }
        df_copy = df_copy.rename(columns=rename_map)
        
        # Check if file exists
        if master_log_path.exists():
            # Read existing log and append new results
            existing_df = pd.read_excel(master_log_path)
            combined_df = pd.concat([existing_df, df_copy], ignore_index=True)
        else:
            combined_df = df_copy
        
        # Rotate log to prevent unbounded growth
        if len(combined_df) > MAX_LOG_ENTRIES:
            combined_df = combined_df.tail(MAX_LOG_ENTRIES)
        
        # Write to Excel with formatting
        with pd.ExcelWriter(master_log_path, engine='openpyxl') as writer:
            combined_df.to_excel(writer, sheet_name='VCP Log', index=False)
            
            # Get workbook and worksheet
            workbook = writer.book
            worksheet = writer.sheets['VCP Log']
            
            # Format header row
            header_fill = PatternFill(start_color="9966CC", end_color="9966CC", fill_type="solid")
            header_font = Font(bold=True, color="FFFFFF")
            
            for cell in worksheet[1]:
                cell.fill = header_fill
                cell.font = header_font
                cell.alignment = Alignment(horizontal="center", vertical="center")
            
            # Auto-adjust column widths
            for column in worksheet.columns:
                max_length = 0
                column_letter = column[0].column_letter
                for cell in column:
                    try:
                        if len(str(cell.value)) > max_length:
                            max_length = len(str(cell.value))
                    except:
                        pass
                adjusted_width = min(max_length + 2, 50)
                worksheet.column_dimensions[column_letter].width = adjusted_width
        
        console.print(f"[green]✅ Master log updated: ./Report/VCP_Master_Log.xlsx[/green]")
        console.print(f"[dim]  Total records: {len(combined_df)}[/dim]")
    except Exception as e:
        console.print(f"[red]Error saving master log:[/red]")
        console.print(f"[red]{type(e).__name__}: {str(e)}[/red]")
        console.print(f"[dim]{traceback.format_exc()}[/dim]")

def load_watchlist_from_json(config_file='watchlists.json'):
    """Load tickers from existing watchlist JSON"""
    try:
        # Resolve relative to script directory so it works regardless of CWD
        config_path = Path(config_file)
        if not config_path.is_absolute():
            config_path = SCRIPT_DIR / config_path
        with open(config_path, 'r') as f:
            markets = json.load(f)
        
        all_tickers = []
        for market_key, config in markets.items():
            if config.get('enabled', True):
                tickers = config['tickers']
                all_tickers.extend(tickers)
        
        # Remove duplicates and warn about known problematic tickers
        unique_tickers = list(set(all_tickers))
        
        # Known delisted/problematic tickers to skip
        known_bad = ['HSI1!.HK', 'BBD.B.TO', 'NCO']
        problematic = [t for t in unique_tickers if t in known_bad]
        if problematic:
            console.print(f"[yellow]⚠️  Skipping known problematic tickers: {', '.join(problematic)}[/yellow]")
            unique_tickers = [t for t in unique_tickers if t not in known_bad]
        
        return unique_tickers
    except FileNotFoundError:
        console.print(f"[red]Watchlist file '{config_path}' not found![/red]")
        return None

# ============================================================================
# MAIN EXECUTION
# ============================================================================
if __name__ == "__main__":
    console.print("[bold magenta]═══════════════════════════════════════════════════[/bold magenta]")
    console.print("[bold magenta]    VCP Pattern Scanner v1.0 (Mark Minervini)     [/bold magenta]")
    console.print("[bold magenta]═══════════════════════════════════════════════════[/bold magenta]")
    console.print(f"[dim]Started at {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}[/dim]")
    
    # Choose watchlist
    console.print("\n[bold cyan]Select watchlist to scan:[/bold cyan]")
    console.print("  1. Tech Sector (Global Tech Stocks)")
    console.print("  2. US Markets (S&P 500 + Nasdaq-100, ~508 tickers)")
    console.print("  3. Japan MSCI (MSCI Japan, 180 tickers)")
    console.print("  4. Hong Kong (HSI + HSTECH Combined, 103 tickers)")
    choice = input("\nEnter choice (1-4) [default: 1]: ").strip() or "1"
    
    if choice == "2":
        watchlist_file = 'watchlists/us_stocks.json'
        console.print(f"[cyan]→ Using {watchlist_file} (SPX + QQQ)[/cyan]")
    elif choice == "3":
        watchlist_file = 'watchlists/japan_stocks.json'
        console.print(f"[cyan]→ Using {watchlist_file} (MSCI Japan, 180 tickers)[/cyan]")
    elif choice == "4":
        watchlist_file = 'watchlists/hk_stocks.json'
        console.print(f"[cyan]→ Using {watchlist_file} (Hong Kong HSI + HSTECH, 103 tickers)[/cyan]")
    else:
        watchlist_file = 'watchlists/tech_sector.json'
        console.print(f"[cyan]→ Using {watchlist_file} (Global Tech Stocks)[/cyan]")
    
    # Load watchlist from JSON
    tickers = load_watchlist_from_json(watchlist_file)
    
    if tickers is None or len(tickers) == 0:
        console.print("[yellow]Using default watchlist...[/yellow]")
        # Default US tech stocks for testing
        tickers = ["AAPL", "MSFT", "NVDA", "GOOGL", "AMZN", "TSLA", "META", "NFLX", 
                   "AMD", "AVGO", "QCOM", "INTC", "CRM", "ORCL", "ADBE"]
    
    console.print(f"[cyan]Loaded {len(tickers)} tickers from watchlist[/cyan]")
    
    # Load or initialize ticker cache
    if is_cache_valid():
        ticker_cache = load_cache()
        cache_age = (time.time() - os.path.getmtime(CACHE_FILE)) / 3600
        console.print(f"[cyan]📦 Cache loaded ({len(ticker_cache)} tickers, {cache_age:.1f}h old, v{CACHE_VERSION})[/cyan]")
    else:
        ticker_cache = {}
        console.print(f"[dim]Cache expired or not found - will build fresh cache (6h expiry)[/dim]")
    
    # Scan for VCP patterns
    results = scan_watchlist(tickers, ticker_cache)
    
    # Save cache for future runs (multi-script safe)
    if CACHE_ENABLED and ticker_cache:
        save_cache(ticker_cache)
    
    # Display results
    display_results(results)
    
    console.print(f"\n[dim]Completed at {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}[/dim]")

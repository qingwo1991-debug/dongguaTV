package com.ednovas.donguatv;

import android.content.pm.ActivityInfo;
import android.os.Build;
import android.os.Bundle;
import android.view.View;
import android.view.ViewGroup;
import android.view.Window;
import android.webkit.JavascriptInterface;
import android.webkit.WebView;
import com.getcapacitor.BridgeActivity;

public class MainActivity extends BridgeActivity {

    private int statusBarHeight = 0;
    private ViewGroup webViewParent = null;
    // 📱 Android 15 (API 35) 及以上版本强制 Edge-to-Edge，需要手动添加 padding
    private boolean needsManualPadding = false;

    @Override
    public void onCreate(Bundle savedInstanceState) {
        super.onCreate(savedInstanceState);

        Window window = getWindow();
        
        // 设置状态栏背景色
        window.setStatusBarColor(0xFF141414);
        
        // 设置状态栏图标为浅色
        View decorView = window.getDecorView();
        int flags = decorView.getSystemUiVisibility();
        flags &= ~View.SYSTEM_UI_FLAG_LIGHT_STATUS_BAR;
        decorView.setSystemUiVisibility(flags);
        
        // 📱 检测是否是 Android 15+ (API 35+)
        // Android 15+ 强制 Edge-to-Edge，需要手动处理 padding
        needsManualPadding = Build.VERSION.SDK_INT >= 35;
        
        if (needsManualPadding) {
            // 获取状态栏高度
            statusBarHeight = getStatusBarHeight();
        }
    }

    @Override
    public void onStart() {
        super.onStart();
        
        // 获取 WebView 并设置其父容器的 padding
        WebView webView = getBridge().getWebView();
        if (webView != null && webView.getParent() instanceof ViewGroup) {
            webViewParent = (ViewGroup) webView.getParent();
            
            // 📱 只在 Android 15+ 上添加手动 padding
            if (needsManualPadding) {
                // 设置父容器的顶部 padding
                webViewParent.setPadding(
                    webViewParent.getPaddingLeft(),
                    statusBarHeight,
                    webViewParent.getPaddingRight(),
                    webViewParent.getPaddingBottom()
                );
                
                // 设置背景色与应用一致
                webViewParent.setBackgroundColor(0xFF141414);
            }
            
            // 添加 JavaScript 接口用于全屏控制（所有版本都需要）
            webView.addJavascriptInterface(new FullscreenInterface(), "AndroidFullscreen");
        }
    }
    
    // 获取状态栏高度（像素）
    private int getStatusBarHeight() {
        int result = 0;
        int resourceId = getResources().getIdentifier("status_bar_height", "dimen", "android");
        if (resourceId > 0) {
            result = getResources().getDimensionPixelSize(resourceId);
        }
        // 如果获取失败，使用默认值
        if (result == 0) {
            result = (int) (24 * getResources().getDisplayMetrics().density);
        }
        return result;
    }
    
    // 进入全屏模式
    private void enterFullscreen() {
        runOnUiThread(() -> {
            // 📱 只在 Android 15+ 上移除手动添加的 padding
            if (needsManualPadding && webViewParent != null) {
                webViewParent.setPadding(0, 0, 0, 0);
            }
            
            // 隐藏状态栏和导航栏
            View decorView = getWindow().getDecorView();
            decorView.setSystemUiVisibility(
                View.SYSTEM_UI_FLAG_IMMERSIVE_STICKY
                | View.SYSTEM_UI_FLAG_FULLSCREEN
                | View.SYSTEM_UI_FLAG_HIDE_NAVIGATION
                | View.SYSTEM_UI_FLAG_LAYOUT_STABLE
                | View.SYSTEM_UI_FLAG_LAYOUT_HIDE_NAVIGATION
                | View.SYSTEM_UI_FLAG_LAYOUT_FULLSCREEN
            );
            
            // 锁定横屏
            setRequestedOrientation(ActivityInfo.SCREEN_ORIENTATION_SENSOR_LANDSCAPE);
        });
    }
    
    // 退出全屏模式
    private void exitFullscreen() {
        runOnUiThread(() -> {
            // 📱 只在 Android 15+ 上恢复手动添加的 padding
            if (needsManualPadding && webViewParent != null) {
                webViewParent.setPadding(
                    webViewParent.getPaddingLeft(),
                    statusBarHeight,
                    webViewParent.getPaddingRight(),
                    webViewParent.getPaddingBottom()
                );
            }
            
            // 显示状态栏
            View decorView = getWindow().getDecorView();
            int flags = decorView.getSystemUiVisibility();
            flags &= ~View.SYSTEM_UI_FLAG_FULLSCREEN;
            flags &= ~View.SYSTEM_UI_FLAG_HIDE_NAVIGATION;
            flags &= ~View.SYSTEM_UI_FLAG_IMMERSIVE_STICKY;
            decorView.setSystemUiVisibility(flags);
            
            // 解锁屏幕方向
            setRequestedOrientation(ActivityInfo.SCREEN_ORIENTATION_UNSPECIFIED);
        });
    }
    
    // JavaScript 接口类
    public class FullscreenInterface {
        @JavascriptInterface
        public void enter() {
            enterFullscreen();
        }
        
        @JavascriptInterface
        public void exit() {
            exitFullscreen();
        }
    }
    
    // 📺 TV 遥控器返回键处理
    @SuppressWarnings("deprecation")
    @Override
    public void onBackPressed() {
        WebView webView = getBridge().getWebView();
        if (webView != null) {
            // 通过 JavaScript 处理完整的导航状态机：弹窗 → 播放页 → 搜索结果 → 退出
            webView.evaluateJavascript(
                "(function() {" +
                "  try {" +
                "    // 1. 关闭选集弹窗" +
                "    var popup = document.getElementById('tv-episode-popup');" +
                "    if (popup) {" +
                "      popup.remove();" +
                "      var epBtn = document.getElementById('tv-select-episode');" +
                "      if (epBtn) epBtn.focus();" +
                "      return 'closed_popup';" +
                "    }" +
                "    // 2. 关闭播放页面（先退出全屏）" +
                "    if (window.vueApp && window.vueApp.showDetail) {" +
                "      if (typeof dp !== 'undefined' && dp && dp.fullScreen) {" +
                "        try { dp.fullScreen.cancel('web'); } catch(e) {}" +
                "      }" +
                "      window.vueApp.closeDetail();" +
                "      return 'closed_detail';" +
                "    }" +
                "    // 3. 从搜索结果返回首页" +
                "    if (window.vueApp && window.vueApp.searched) {" +
                "      window.vueApp.goHome();" +
                "      return 'went_home';" +
                "    }" +
                "    // 4. 已在首页，交给系统退出" +
                "    return 'exit';" +
                "  } catch(e) { return 'exit'; }" +
                "})()",
                result -> {
                    if (result != null && result.contains("exit")) {
                        runOnUiThread(() -> {
                            // 首页按返回，退出应用
                            MainActivity.super.onBackPressed();
                        });
                    }
                }
            );
        } else {
            super.onBackPressed();
        }
    }
}


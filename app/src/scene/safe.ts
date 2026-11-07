// How much of the screen the HUD covers at the top and bottom (CSS px), so the camera fits the
// table into the band between them while the canvas itself stays full-bleed behind everything.
export const safeArea = { top: 0, bottom: 0 };

export const reducedMotion = typeof matchMedia !== "undefined" && matchMedia("(prefers-reduced-motion: reduce)").matches;

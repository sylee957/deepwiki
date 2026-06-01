import VersoManual
import Book

open Verso.Genre Manual

/-- Entry point for rendering the book to HTML: `lake exe generate-book`. -/
def main := manualMain (%doc Book)

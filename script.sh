#!/bin/bash

# Crear directorios de salida y diferencias si no existen
mkdir -p ./ejemplos/misalida
mkdir -p ./ejemplos/diferencias

# Variables para almacenar archivos con diferencias
diferencias_lint=()
diferencias_sug=()

# Ejecutar Linter en modo compilación (-c) y guardar salidas
for i in {01..27}; do
  archivo="./ejemplos/caso${i}.mhs"
  salida="./ejemplos/misalida/caso${i}-lint.mhs"
  
  if [[ -f "$archivo" ]]; then
    echo "Generando salida en modo compilación para $archivo"
    ./Linter -c "$archivo" > "$salida"
  else
    echo "Advertencia: El archivo $archivo no existe"
  fi
done

# Ejecutar Linter en modo sugerencias (-s) y guardar salidas
for i in {01..27}; do
  archivo="./ejemplos/caso${i}.mhs"
  salida="./ejemplos/misalida/caso${i}-sug"
  
  if [[ -f "$archivo" ]]; then
    echo "Generando salida en modo sugerencias para $archivo"
    ./Linter -s "$archivo" > "$salida"
  else
    echo "Advertencia: El archivo $archivo no existe"
  fi
done

# Comparar archivos generados con los de referencia para -lint
for i in {01..27}; do
  archivo_ref="./ejemplos/salidas/caso${i}-lint.mhs"
  archivo_gen="./ejemplos/misalida/caso${i}-lint.mhs"
  diferencia="./ejemplos/diferencias/diferencias_caso${i}-lint.txt"
  
  echo "Procesando archivo caso${i}-lint.mhs"
  if [[ -f "$archivo_ref" && -f "$archivo_gen" ]]; then
    diff -w "$archivo_ref" "$archivo_gen" > "$diferencia"
    if [[ $? -ne 0 ]]; then
      echo "✘ Diferencias encontradas para caso${i}-lint.mhs, revisar $diferencia."
      diferencias_lint+=("caso${i}-lint.mhs")
    else
      rm "$diferencia"  # Opcional: elimina el archivo de diferencias si no hay cambios
    fi
  else
    echo "Advertencia: Uno de los archivos $archivo_ref o $archivo_gen no existe"
  fi
done

# Comparar archivos generados con los de referencia para -sug
for i in {01..27}; do
  archivo_ref="./ejemplos/salidas/caso${i}-sug"
  archivo_gen="./ejemplos/misalida/caso${i}-sug"
  diferencia="./ejemplos/diferencias/diferencias_caso${i}-sug.txt"
  
  echo "Procesando archivo caso${i}-sug"
  if [[ -f "$archivo_ref" && -f "$archivo_gen" ]]; then
    diff -w "$archivo_ref" "$archivo_gen" > "$diferencia"
    if [[ $? -ne 0 ]]; then
      echo "✘ Diferencias encontradas para caso${i}-sug, revisar $diferencia."
      diferencias_sug+=("caso${i}-sug")
    else
      rm "$diferencia"  # Opcional: elimina el archivo de diferencias si no hay cambios
    fi
  else
    echo "Advertencia: Uno de los archivos $archivo_ref o $archivo_gen no existe"
  fi
done

# Resumen final de archivos con diferencias
echo ""
echo "====================================="
echo "           RESUMEN FINAL"
echo "====================================="

if [[ ${#diferencias_lint[@]} -gt 0 ]]; then
  echo "Archivos lint con diferencias:"
  for archivo in "${diferencias_lint[@]}"; do
    echo " - $archivo"
  done
else
  echo "✔ Todos los archivos lint coinciden con los de referencia."
fi

echo ""

if [[ ${#diferencias_sug[@]} -gt 0 ]]; then
  echo "Archivos sug con diferencias:"
  for archivo in "${diferencias_sug[@]}"; do
    echo " - $archivo"
  done
else
  echo "✔ Todos los archivos sug coinciden con los de referencia."
fi

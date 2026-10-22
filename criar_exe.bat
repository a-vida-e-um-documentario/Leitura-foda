@echo off
chcp 65001 >nul
title Criar o programa Leitura Foda
echo.
echo ===== Leitura Foda - criar o programa (.exe) =====
echo.
echo 1/2  Instalando as bibliotecas necessarias...
python -m pip install --upgrade pyinstaller customtkinter pillow
if errorlevel 1 goto erro
echo.
echo 2/2  Criando o programa (pode demorar alguns minutos)...
python -m PyInstaller --noconfirm --clean --onefile --windowed --name "Leitura Foda" --icon icone.ico --add-data "icone.ico;." --collect-all customtkinter leitura_foda.py
if errorlevel 1 goto erro
echo.
echo ===== PRONTO! =====
echo O programa esta em:  dist\Leitura Foda.exe
echo Pode copiar esse arquivo para onde quiser (Area de Trabalho, pen drive...).
echo Seus dados continuam na pasta .leitura_foda dentro da sua pasta de usuario.
echo.
pause
exit /b 0

:erro
echo.
echo Algo deu errado. Confira se o Python esta instalado e se esta pasta tem os arquivos:
echo   leitura_foda.py  e  icone.ico
echo Se o erro citar a versao do Python, tente com o Python 3.12 ou 3.13.
echo.
pause
exit /b 1

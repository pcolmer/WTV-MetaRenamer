REM This file can be used to run WTV-MetaRenamer from the Task Scheduler. Keep this in the
REM same directory as WTV-MetaRenamer.ps1
@echo off
cd /d "%~dp0"
powershell -NoProfile -ExecutionPolicy Bypass -File .\wtv-metarenamer.ps1 %*

# Flow Free Solver GUI
![_2025_02_18_20_01_38_612-ezgif com-video-to-gif-converter](https://github.com/user-attachments/assets/a7e5b18e-3e12-4ab4-aabf-e7d194efd415) <BR> <BR>


SAT(Boolean Satisfiability) solver와 Tkinter GUI를 사용하여 Flow Free 퍼즐을 푸는 파이썬 프로그램입니다.

<BR>

## 📅 마지막 정상 작동 확인 날짜 및 버전
- **DATE**: 2024-02-18

<BR>

## 🔍 주요 기능
- **SAT solver 활용**: `pycosat` 라이브러리를 사용하여 Flow Free 퍼즐을 SAT 문제로 변환하고 해결합니다.
- **Tkinter GUI**: 사용자 친화적인 그래픽 인터페이스를 제공하여 퍼즐을 시각적으로 입력하고 해결 과정을 확인할 수 있습니다.
- **자동 퍼즐 해결**: 퍼즐을 입력하면 SAT 솔버를 통해 자동으로 해를 찾아 Canvas에 시각적으로 표시합니다.
- **다양한 설정 옵션**: 셀 크기, 선 굵기 등 GUI 설정을 사용자가 조절할 수 있습니다.

<BR>

## 💾 다운로드 <BR>
| Program                                | URL                                                | 필수여부 | 비고                                                                                           |
|----------------------------------------|----------------------------------------------------|----------|------------------------------------------------------------------------------------------------|
| `Python`            | [Download](https://www.python.org/downloads/)   | 필수     | ◼ Python Script 동작, 파이썬 3.9.0 버전 또는 그 이상 권장 |
| `반디집`             | [Download](https://kr.bandisoft.com/bandizip/)   | 필수     | ◼ (* 다른 압축 프로그램 사용 가능) |

<BR>

## 🛠️ 설치

1. Python 을 설치합니다. <BR> <BR>
**[ ※ 주의 ] Python 설치 시 Add python.exe to PATH 에 체크 후 Install Now 클릭** <BR>
(📌 미처 누르지 못했다면 설치 파일 다시 실행 또는 제거 후 재 설치) <BR> <BR>
**(선택) 설치 후 Disable path length limit 기능을 사용할 수 있도록 클릭** <BR> <BR>

2. **(필수) pycosat Package 설치** <BR> <BR>
(* 두 코드 중 하나 선택) <BR>
`pip install pycosat` <BR>
or <BR>
`python -m pip install pycosat` <BR> <BR>
**[ ※ 주의 ] 만약 위 명령어 사용 중 ERROR: Could not install packages due to an EnvironmentError: [WinError 5] 액세스가 거부되었습니다: (생략) Consider using the `--user` option or check the permissions. 과 같은 오류가 나왔다면 끝에 `--user`를 붙여서 입력** <BR> <BR>
(* 권한 오류 발생시 두 코드 중 하나 선택) <BR>
`pip install pycosat --user` <BR>
or <BR>
`python -m pip install pycosat --user` <BR>

<BR>

## ⏩ 사용 방법

### 1. **스크립트 실행**

`Flow Free Solver GUI.py` 를 실행합니다. <BR> <BR>

### 2. **GUI 조작**: 

   - **Grid Size**: 텍스트 상자에 원하는 Grid 크기를 입력하고 "Create Grid" 버튼을 클릭하여 퍼즐 입력 Grid를 생성합니다.
   - **Cell Size & Line Size**: "Size Options" Frame에서 Cell 크기와 Line 굵기를 조절하고 "Apply Cell Size", "Apply Line Size" 버튼을 클릭하여 적용합니다.
   - **Color Palette**: "Color Options" Frame에서 원하는 색상을 선택합니다.
   - **퍼즐 입력**: Canvas에서 색상을 지정할 Cell을 클릭하여 시작점과 끝점을 표시합니다. 같은 색상을 다시 클릭하면 제거됩니다.
   - **Solve Puzzle**: "Display" Frame의 "Solve Puzzle" 버튼을 클릭하여 퍼즐을 해결합니다. Canvas에 해답이 시각적으로 표시됩니다.
     
<BR>

## 📃 출처
이 Flow Free Solver GUI는 다음 자료를 기반으로 제작되었습니다.

- **기본 코드**: [mzucker/flow_solver](https://github.com/mzucker/flow_solver)
- **참고 자료**: [mzucker's blog post: Solving Flow Puzzles using SAT](https://mzucker.github.io/2016/08/28/flow-solver.html)

**이 GUI 프로그램의 기본적인 로직은 `mzucker/flow_solver` 프로젝트에서 가져왔으며, Tkinter GUI 및 사용자 인터페이스는 본 프로젝트에서 새롭게 구현되었습니다.**

<BR>

## ⚖️ 라이센스
이 프로젝트는 [MIT License](LICENSE)에 따라 라이선스가 부여됩니다.

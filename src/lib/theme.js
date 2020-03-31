const theme = {
  buttons: {
    small: {
      fontSize: '12px',
      fontWeight: 'normal',
      padding: '5px 10px'
    },
    normal: {
      fontSize: '14px',
      fontWeight: 'normal',
      height: '35px',
      padding: '5px 10px'
    }
  },
  font: {
    align: {
      center: 'center',
      initial: 'initial',
      left: 'left',
      right: 'right'
    },
    size: {
      big: '18px',
      inherit: 'inherit',
      normal: '16px',
      small: '10px'
    },
    weight: {
      normal: 'normal',
      medium: 'medium',
      bold: 'bold'
    }
  }
};

const darkTheme = {
  background: '#111111',
  outlineColor: 'rgba(255,255,255,0.6)',
  textColor: 'rgba(255,255,255,0.6)',
  buttonColor: '#ff0e1f',
  modalColor: '#111111'
};

const lightTheme = {
  background: '#ffffff',
  outlineColor: '#111111',
  textColor: 'rgba(255,255,255,0.6)',
  buttonColor: '#ff0e1f',
  modalColor: '#ffffff'
};

export { darkTheme, lightTheme };

export default theme;

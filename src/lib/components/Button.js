import styled, { css } from 'styled-components';

export const Button = styled.button`
  -webkit-appearance: none;
  background-color: ${props => props.theme.colors.buttonColor};
  color: ${props => props.theme.colors.outlineColor};
  border: 0;
  cursor: pointer;
  display: inline-block;
  letter-spacing: 1px;
  line-height: 1;
  outline: none;
  overflow: hidden;
  padding: 0;
  text-decoration: none;
  transition: all 0.3s;
  user-select: none;
  white-space: nowrap;
  ${props => {
    if (props.size) {
      return css`
        font-size: ${props.theme.buttons[props.size].fontSize};
        font-weight: ${props.theme.buttons[props.size].fontWeight};
        height: ${props.theme.buttons[props.size].height};
        padding: ${props.theme.buttons[props.size].padding};
      `;
    }
  }}
`;

export const DeleteImageButton = styled(Button)`
  align-items: center;
  border: none;
  display: flex;
  flex-shrink: 0;
  height: 1.5rem;
  justify-content: center;
  padding-right: 0.5px;
  position: absolute;
  right: 0.5rem;
  top: 0.5rem;
  width: 1.5rem;
  z-index: 10;
  background: none;
  &:before,
  &:after {
    background: #ff0e1f;
    border-radius: 2px;
    content: '';
    display: block;
    height: 0.1rem;
    left: 50%;
    position: absolute;
    top: 50%;
    transition: 0.3s all;
    width: 2rem;
  }

  &:before {
    transform: translate(-50%, -50%) rotate(45deg);
  }

  &:after {
    transform: translate(-50%, -50%) rotate(-45deg);
  }
`;

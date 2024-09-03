import styled, { css } from 'styled-components';

const FlexBox = styled.div.withConfig({
  shouldForwardProp: prop => !['alignItems', 'column', 'flex', 'justifyContent'].includes(prop)
})`
  align-items: ${props => props.alignItems};
  display: flex;
  flex-direction: ${props => (props.column ? 'column' : 'row')};
  justify-content: ${props => props.justifyContent};
  margin-bottom: 0;

  ${props => {
    if (props.flex) {
      return css`
        flex: ${props.flex};
      `;
    }
  }}
`;

FlexBox.defaultProps = {
  alignItems: 'initial',
  justifyContent: 'intial'
};

export default FlexBox;
